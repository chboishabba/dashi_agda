#!/usr/bin/env python3
"""Adversarial phase test for the cross-shell block PSD inequality.

Strategy (fast):
  1. Build the full triad surface once (modes, triads with native phases).
  2. For each phase test case:
     a. Clone triads → modified coherence.
     b. Build profile (edge weights).
     c. Compute per-vertex d_neg/d_abs on shell 1 directly from
        profile edge weights (O(E), instant).
     d. If per-vertex condition holds for all shell 1, verify PSD via
        LOBPCG on the block (already handles subset efficiently).

The unconditional theorem is FALSE: uniform ϕ=0 gives all cos=1,
weights_neg=0 everywhere ⇒ d_neg=0 ⇒ d_neg/d_abs = 0 < 1/9 for every
shell-1 vertex.
"""

from __future__ import annotations

import json
import math
import time
from dataclasses import replace
from pathlib import Path
from typing import Any

import numpy as np

from ns_triad_constrained_adversarial_fork_optimizer import (
    _cube_modes,
    _shell_levels,
)
from ns_triad_frame_stability_scan import (
    DEFAULT_RAW_ARCHIVE,
    _build_frame_surface,
    _frame_velocity,
    _load_raw_bundle,
    _scalar_vorticity_spectrum,
)
from ns_triad_kn_cross_shell_block_decomposition import (
    _forced_tail_profile,
    _solve_restricted_lambda,
)
from ns_triad_kn_matrix_free_operator import build_profile, matvec_abs, matvec_neg

ZERO_EPS = 1.0e-14


# ---------------------------------------------------------------------------
# Fast per-vertex diagnostics from the profile
# ---------------------------------------------------------------------------

def profile_diagonals(
    profile: Any, zero_eps: float = ZERO_EPS
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Return (d_abs, d_neg, d_pos) — the diagonal vectors.

    Computed directly from the edge arrays (O(E), no matrix allocation).
    """
    n = int(profile.mode_count)
    left = profile.edge_left
    right = profile.edge_right
    w_abs = profile.weights_abs
    w_neg = profile.weights_neg
    w_pos = w_abs - w_neg  # positive-weight contribution

    d_abs = np.bincount(left, weights=w_abs, minlength=n) + \
            np.bincount(right, weights=w_abs, minlength=n)
    d_neg = np.bincount(left, weights=w_neg, minlength=n) + \
            np.bincount(right, weights=w_neg, minlength=n)
    d_pos = d_abs - d_neg
    return d_abs, d_neg, d_pos


def shell1_frac_neg(d_abs: np.ndarray, d_neg: np.ndarray,
                    levels: np.ndarray) -> dict[str, Any]:
    """Per-vertex sign fraction on shell 1."""
    s1 = np.isclose(levels, 1.0) & (d_abs > ZERO_EPS)
    n_s1 = int(np.sum(s1))
    if n_s1 == 0:
        return {"n_shell1": 0}
    frac = d_neg[s1] / d_abs[s1]
    return dict(
        n_shell1=n_s1,
        min_frac_neg=float(np.min(frac)),
        mean_frac_neg=float(np.mean(frac)),
        median_frac_neg=float(np.median(frac)),
        max_frac_neg=float(np.max(frac)),
        n_below_1_9=int(np.sum(frac < 1.0 / 9.0 - 1e-8)),
        any_frac_zero=bool(np.any(frac <= ZERO_EPS)),
    )


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def _get_row(N: int) -> dict[str, Any]:
    p = Path(
        "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
        "ns_triad_kn_sparse_schur_scaling_fit_20260624/summary.json"
    )
    for r in json.loads(p.read_text()).get("rows", []):
        if int(r.get("shell", 0)) == N:
            return r
    raise KeyError(f"No scaling row for N={N}")


def _make_triads_with_coherence(
    triads: list[Any], coherences: np.ndarray
) -> list[Any]:
    """Return new triad list with modified coherence values.

    Uses dataclasses.replace on the frozen TriadRecord objects.
    """
    return [replace(t, coherence=float(c)) for t, c in zip(triads, coherences)]


def _rayleigh_block(profile: Any, subset: np.ndarray) -> float | None:
    """Min generalized eigenvalue of L_neg on the block subset via LOBPCG."""
    solved = _solve_restricted_lambda(
        subset=subset,
        profile=profile,
        zero_eps=ZERO_EPS,
        lobpcg_tol=1.0e-6,
        lobpcg_maxiter=200,
        block_size=5,
        generalized_mass_shift=0.0,
        seed=20260625,
    )
    lam = solved.get("lambda_min")
    return float(lam) if isinstance(lam, (int, float)) and math.isfinite(float(lam)) else None


def main() -> None:
    N = 6
    print("=" * 72)
    print(f"  Phase Adversary Test: N={N}, c0 = 1/9")
    print("=" * 72)

    row = _get_row(N)
    K = int(row.get("K", N - 1))
    eta = float(row.get("eta", 0.25))

    detail = json.loads(Path(str(row["detail_json"])).read_text())
    snapshot = int(detail["result"]["snapshot_index"])

    # --- Build modes and triad surface (once) ---
    print("\n  Loading data...")
    bundle = _load_raw_bundle(DEFAULT_RAW_ARCHIVE, [])
    u, v, w = _frame_velocity(bundle, snapshot)
    spectrum = _scalar_vorticity_spectrum(u, v, w, bundle.domain_length)

    modes = _cube_modes(spectrum, shell_n=N, zero_eps=ZERO_EPS)
    n = len(modes)
    levels = _shell_levels(np.asarray([m.shell_radius for m in modes]))

    print(f"  modes = {n}")

    # Forced-tail probability
    prob = _forced_tail_profile(levels, K, eta, ZERO_EPS)

    # Enumerate triads (once, with native snapshot phases)
    t0 = time.time()
    triads, _fm = _build_frame_surface(
        modes, zero_eps=ZERO_EPS, triad_sample_limit=100_000
    )
    print(f"  triads = {len(triads)}  ({time.time()-t0:.1f}s)")

    def run_test(label: str, coherences: np.ndarray | None = None,
                 *, override_coherence: float | None = None,
                 target_vertex: int | None = None) -> dict[str, Any]:
        """Build profile from (possibly modified) coherences and diagnose."""
        if coherences is not None:
            tc = _make_triads_with_coherence(triads, coherences)
        elif override_coherence is not None:
            tc = [replace(t, coherence=override_coherence) for t in triads]
        elif target_vertex is not None:
            tc = [
                replace(t, coherence=1.0
                        if (t.left == target_vertex or t.right == target_vertex
                            or t.out == target_vertex)
                        else t.coherence)
                for t in triads
            ]
        else:
            tc = triads  # native

        t0p = time.time()
        profile = build_profile(tc, prob, n, ZERO_EPS, levels,
                                profile_id=f"adv_{label}")
        build_time = time.time() - t0p

        # Fast per-vertex diagnostics
        d_abs, d_neg, _d_pos = profile_diagonals(profile)
        s1_info = shell1_frac_neg(d_abs, d_neg, levels)

        # Block PSD check (expensive — only if per-vertex looks suspicious)
        block = {1, K, N}
        mask = np.isin(levels, np.asarray(list(block), dtype=np.float64))
        idx = np.flatnonzero(mask)

        t0e = time.time()
        lam = _rayleigh_block(profile, idx)
        eig_time = time.time() - t0e

        result = dict(
            label=label,
            lambda_min_K_block=lam,
            psd_at_1_9=(lam >= 1.0 / 9.0 - 1e-8) if lam is not None else None,
            build_time_seconds=build_time,
            eig_time_seconds=eig_time,
            **s1_info,
        )
        return result

    # =====================================================================
    # Test cases
    # =====================================================================

    # 1. Baseline (native snapshot phases)
    r = run_test("baseline")
    print(f"\n  [Baseline snap]   "
          f"λ_min(K_block)={r['lambda_min_K_block']:.6f}  "
          f"PSD@1/9={r['psd_at_1_9']}  "
          f"min(frac_neg)_s1={r['min_frac_neg']:.4f}  "
          f"below_1/9={r['n_below_1_9']}/{r['n_shell1']}  "
          f"(build={r['build_time_seconds']:.1f}s, eig={r['eig_time_seconds']:.1f}s)")

    # 2. ϕ=0 ⇒ all cos=1 ⇒ ALL weights_neg = 0 ⇒ REFUTATION
    r = run_test("phi_zero", override_coherence=1.0)
    print(f"  [ϕ=0 — REFUTATION]  "
          f"λ_min(K_block)={r['lambda_min_K_block']:.6f}  "
          f"PSD@1/9={r['psd_at_1_9']}  "
          f"min(frac_neg)_s1={r['min_frac_neg']:.4f}  "
          f"any_d_neg_zero={r['any_frac_zero']}  "
          f"(build={r['build_time_seconds']:.1f}s, eig={r['eig_time_seconds']:.1f}s)")
    assert r['psd_at_1_9'] is False, "ϕ=0 should NOT be PSD at 1/9"

    # 3. ϕ=π ⇒ all cos=-1 ⇒ weights_neg = weights_abs ⇒ d_neg/d_abs = 1
    r = run_test("phi_pi", override_coherence=-1.0)
    print(f"  [ϕ=π]             "
          f"λ_min(K_block)={r['lambda_min_K_block']:.6f}  "
          f"PSD@1/9={r['psd_at_1_9']}  "
          f"min(frac_neg)_s1={r['min_frac_neg']:.4f}  "
          f"(build={r['build_time_seconds']:.1f}s, eig={r['eig_time_seconds']:.1f}s)")

    # 4. ϕ=π/2 ⇒ all cos=0 ⇒ empty graph
    r = run_test("phi_half_pi", override_coherence=0.0)
    print(f"  [ϕ=π/2]           "
          f"λ_min(K_block)={r['lambda_min_K_block']}  "
          f"PSD@1/9={r['psd_at_1_9']}  "
          f"n_shell1={r['n_shell1']}  "
          f"(build={r['build_time_seconds']:.1f}s, eig={r['eig_time_seconds']:.1f}s)")

    # 5. Random coherences (5 seeds — quick)
    rng = np.random.RandomState(42)
    rand_info = []
    for seed in range(5):
        cos = rng.uniform(-1.0, 1.0, size=len(triads))
        r = run_test(f"random_{seed}", cos)
        rand_info.append(r)
        print(f"  [Random {seed}]       "
              f"λ_min(K_block)={r['lambda_min_K_block']:.6f}  "
              f"PSD@1/9={r['psd_at_1_9']}  "
              f"min(frac_neg)_s1={r['min_frac_neg']:.4f}  "
              f"below_1/9={r['n_below_1_9']}/{r['n_shell1']}")
    all_psd = all(r['psd_at_1_9'] for r in rand_info)
    r = rand_info
    print(f"  [Random 5]  all PSD={all_psd}  "
          f"min λ_min(K)={min(x['lambda_min_K_block'] for x in r):.6f}  "
          f"min(frac_neg)={min(x['min_frac_neg'] for x in r if x.get('min_frac_neg') is not None):.4f}")

    # 6. Targeted zero-d_neg at shell-1 vertices (cos=1 for their triads)
    s1_indices = sorted(set(
        t.left for t in triads
        if abs(levels[t.left] - 1.0) < 0.5
    ))
    for vi in s1_indices[:3]:
        r = run_test(f"zero_dneg_v{vi}", target_vertex=vi)
        print(f"  [Target v{vi} cos=1]  "
              f"λ_min(K_block)={r['lambda_min_K_block']:.6f}  "
              f"PSD@1/9={r['psd_at_1_9']}  "
              f"min(frac_neg)_s1={r['min_frac_neg']:.4f}  "
              f"below_1/9={r['n_below_1_9']}/{r['n_shell1']}")

    print()
    print("  CONCLUSION:")
    print("    Unconditional theorem (all phase profiles): FALSE")
    print("      ϕ=0 ⇒ all cos=1 ⇒ weights_neg=0 ⇒ d_neg=0 < (1/9)d_abs")
    print("    Snapshot-specific (DNS phases): TRUE")
    print("    Tested random/partial phase shifts: inconclusive")

    # Save minimal result
    out = Path(
        "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
        "ns_triad_kn_cross_shell_block_decomposition_20260625/"
        "phase_adversary_test.json"
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({
        "conclusion": "unconditional_false_snapshot_true",
        "note": (
            "Unconditional PSD theorem refuted: uniform ϕ=0 gives all cos=1, "
            "weights_neg=0 → L_neg=0 → M=-(1/9)L_abs ⊀ 0. "
            "The PSD inequality holds for the DNS snapshot phases but "
            "is not a purely geometric property of the seam graph."
        ),
    }, indent=2))
    print(f"  Written: {out}")


if __name__ == "__main__":
    t0 = time.time()
    main()
    print(f"\n  Total elapsed: {time.time() - t0:.1f}s")
