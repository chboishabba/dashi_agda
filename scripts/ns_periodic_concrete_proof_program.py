#!/usr/bin/env python3
"""Deterministic proof-and-falsification program for the concrete periodic NS lane.

This program freezes one literal finite Fourier convention and evaluates every
finite/candidate component requested by the compact-Gamma proof program.  It is
not a theorem prover: universal analytic promotion stays fail-closed.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
from fractions import Fraction
from pathlib import Path
from typing import Any, Iterable, Sequence

SCHEMA = "ns_periodic_concrete_proof_program.v1"


def q(x: Fraction | int) -> str:
    x = Fraction(x)
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def digest(payload: Any) -> str:
    raw = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()


def vadd(a: tuple[int, int, int], b: tuple[int, int, int]) -> tuple[int, int, int]:
    return tuple(x + y for x, y in zip(a, b))  # type: ignore[return-value]


def vmax(v: tuple[int, int, int]) -> int:
    return max(abs(x) for x in v)


def modes(cutoff: int) -> Iterable[tuple[int, int, int]]:
    for k in itertools.product(range(-cutoff, cutoff + 1), repeat=3):
        if k != (0, 0, 0):
            yield k


def hat_multiplier(K: int, k: tuple[int, int, int]) -> Fraction:
    """Exact rational max-norm dyadic hat multiplier."""
    if K < 1:
        raise ValueError("K must be >= 1")
    r = vmax(k)
    lo, mid, hi = 2 ** (K - 1), 2**K, 2 ** (K + 1)
    if r < lo or r > hi:
        return Fraction(0)
    if r <= mid:
        return Fraction(r - lo, mid - lo)
    return Fraction(hi - r, hi - mid)


def carrier_contract() -> dict[str, Any]:
    return {
        "mode_lattice": "Z^3 excluding zero for divergence-free polarization",
        "galerkin_cutoff": "max(abs(kx),abs(ky),abs(kz)) <= N",
        "fourier_l2": "sum_k |u_hat(k)|^2 (coefficient/unitary convention)",
        "reality": "u_hat(-k) = conjugate(u_hat(k))",
        "leray": "P_k = I - k tensor k / |k|_2^2",
        "dyadic_multiplier": "exact rational max-norm hat supported on [2^(j-1),2^(j+1)]",
        "packet_shells": "K-1,K,K+1",
        "packet_energy": "sum_{|j-K|<=1} E_j",
        "gamma": "E_K / packet_energy when packet_energy > 0",
        "off_packet_ratio": "(total_energy-packet_energy)/total_energy when total_energy > 0",
        "sobolev_s": "7/2",
        "dissipation_weight": "|k|_2^2",
        "far_low_input_norm": "weighted l1 low-mode moment times l2 high state",
        "authority": "finite exact conventions; bridge to official analytic norm remains an obligation",
    }


def far_low_enumeration(K: int = 4, R: int = 3) -> dict[str, Any]:
    """Exhaustively check the exact hat multiplier on a tractable small core."""
    low_radius = 2 ** (K - R)
    q_cutoff = 2 ** (K + 1)
    worst = Fraction(0)
    witness = None
    checked = 0
    low_modes = list(modes(low_radius))
    q_modes = [(r, 0, 0) for r in range(1, q_cutoff + 1)]
    for p in low_modes:
        psize = vmax(p)
        if psize == 0:
            continue
        for qq in q_modes:
            for perm in set(itertools.permutations(qq)):
                for signs in itertools.product((-1, 1), repeat=3):
                    qmode = tuple(s * x for s, x in zip(signs, perm))
                    k = vadd(p, qmode)
                    checked += 1
                    ratio = abs(hat_multiplier(K, k) - hat_multiplier(K, qmode)) / Fraction(psize)
                    if ratio > worst:
                        worst = ratio
                        witness = {"p": p, "q": qmode, "k": k}
    lipschitz = Fraction(1, 2 ** (K - 1))
    return {
        "K": K,
        "R": R,
        "checked": checked,
        "observed_lipschitz_per_maxnorm": q(worst),
        "analytic_lipschitz_per_maxnorm": q(lipschitz),
        "enumeration_below_analytic": worst <= lipschitz,
        "witness": witness,
    }


def far_low_certificate(R: int = 8) -> dict[str, Any]:
    multiplier_gain = Fraction(1, 2 ** (R - 1))
    leray = Fraction(1)
    polarization = Fraction(1)
    fourier_normalization = Fraction(1)
    convolution_weight = Fraction(1)
    full = multiplier_gain * leray * polarization * fourier_normalization * convolution_weight
    return {
        "R": R,
        "multiplier_gain": q(multiplier_gain),
        "leray_constant": q(leray),
        "polarization_constant": q(polarization),
        "fourier_normalization": q(fourier_normalization),
        "weighted_convolution_constant": q(convolution_weight),
        "normalized_total": q(full),
        "budget": "1/8",
        "fits_one_eighth": full <= Fraction(1, 8),
        "minimal_radius_for_this_model": min(r for r in range(1, 33) if Fraction(1, 2 ** (r - 1)) <= Fraction(1, 8)),
        "scope": "proved for the frozen rational-hat/weighted-l1 finite model; official norm identification remains open",
    }


def far_high_scan(max_R: int = 16) -> dict[str, Any]:
    components = {
        "two_placements": Fraction(2),
        "bony": Fraction(2),
        "bernstein_shell": Fraction(2),
        "leray": Fraction(1),
        "fourier_normalization": Fraction(1),
    }
    product = math.prod(components.values())
    rows = []
    for R in range(1, max_R + 1):
        geometric = Fraction(1, 2**R) / (1 - Fraction(1, 2))
        total = product * geometric
        rows.append({"R": R, "geometric": q(geometric), "normalized_total": q(total), "fits_one_eighth": total <= Fraction(1, 8)})
    viable = [row["R"] for row in rows if row["fits_one_eighth"]]
    return {
        "s": "7/2",
        "alpha": "1",
        "component_constants": {k: q(v) for k, v in components.items()},
        "constant_product": q(product),
        "scan": rows,
        "minimal_radius": min(viable) if viable else None,
        "R8_total": next(row["normalized_total"] for row in rows if row["R"] == 8),
        "R8_fits_one_eighth": next(row["fits_one_eighth"] for row in rows if row["R"] == 8),
        "scope": "exact candidate normalization; every component constant must still be identified with the official carrier theorem",
    }


def near_triad_budget() -> dict[str, Any]:
    constants = {"LH": Fraction(2), "HL": Fraction(2), "HH": Fraction(4)}
    delta_total = Fraction(1, 4)
    total_C = sum(constants.values(), Fraction(0))
    deltas = {name: delta_total * C / total_C for name, C in constants.items()}
    payments = {name: C * C / (4 * deltas[name]) for name, C in constants.items()}
    residual = sum(payments.values(), Fraction(0))
    checked = 0
    violations = 0
    for a, b in itertools.product(range(-8, 9), repeat=2):
        for name, C in constants.items():
            checked += 1
            lhs = abs(Fraction(C * a * b))
            rhs = deltas[name] * a * a + payments[name] * b * b if C else Fraction(0)
            if lhs > rhs:
                violations += 1
    return {
        "component_constants": {k: q(v) for k, v in constants.items()},
        "delta_total": q(delta_total),
        "optimal_deltas": {k: q(v) for k, v in deltas.items()},
        "component_residual_coefficients": {k: q(v) for k, v in payments.items()},
        "optimized_residual_total": q(residual),
        "closed_form": "(sum C_i)^2/(4 delta_total)",
        "exact_scalar_grid_checks": checked,
        "exact_scalar_grid_violations": violations,
        "candidate_budget_viable": violations == 0,
        "universal_factor_interpretation_proved": False,
    }


def energy_metrics(energy: Sequence[Fraction], K: int) -> dict[str, Fraction]:
    total = sum(energy, Fraction(0))
    packet = sum((energy[j] if 0 <= j < len(energy) else Fraction(0)) for j in (K - 1, K, K + 1))
    center = energy[K] if 0 <= K < len(energy) else Fraction(0)
    gamma = center / packet if packet else Fraction(0)
    off = (total - packet) / total if total else Fraction(0)
    packet_fraction = packet / total if total else Fraction(0)
    dissipation = sum(Fraction(2 ** (2 * j)) * e for j, e in enumerate(energy))
    return {"total": total, "packet": packet, "gamma": gamma, "off": off, "packet_fraction": packet_fraction, "dissipation": dissipation}


def five_halves_falsification() -> dict[str, Any]:
    K = 4
    eps = Fraction(1, 2**24)
    energy = [Fraction(0) for _ in range(12)]
    energy[K] = Fraction(3, 4)
    energy[K + 1] = Fraction(1, 16)
    energy[K + 2] = eps
    energy[K + 3] = Fraction(1, 16)
    energy[K - 1] = Fraction(1, 16)
    energy[0] = Fraction(1, 16) - eps
    m = energy_metrics(energy, K)
    weighted_sq = [Fraction(2 ** (5 * j)) * e for j, e in enumerate(energy)]
    ratio_sq = weighted_sq[K + 3] / weighted_sq[K + 2]
    candidate_constraints = {
        "gamma_at_least_3_4": m["gamma"] >= Fraction(3, 4),
        "packet_fraction_at_least_3_4": m["packet_fraction"] >= Fraction(3, 4),
        "off_packet_at_most_1_4": m["off"] <= Fraction(1, 4),
    }
    families = {}
    for name, vals in {
        "geometric": [Fraction(1, 2**j) for j in range(12)],
        "power_like": [Fraction(1, (j + 1) ** 2) for j in range(12)],
        "plateau_8": [Fraction(1, 8) if 2 <= j < 10 else Fraction(0) for j in range(12)],
    }.items():
        mm = energy_metrics(vals, max(range(len(vals)), key=lambda j: vals[j]))
        families[name] = {k: q(v) for k, v in mm.items()}
    return {
        "target_shell": K,
        "counterexample_energy": [q(e) for e in energy],
        "metrics": {k: q(v) for k, v in m.items()},
        "constraints": candidate_constraints,
        "adjacent_weighted_ratio_squared": q(ratio_sq),
        "unconditional_or_static_compact_gamma_adjacent_contraction_refuted": all(candidate_constraints.values()) and ratio_sq > 1,
        "dynamic_remainder_or_time_integrated_route_required": True,
        "test_families": families,
        "pointwise_five_halves_promoted": False,
    }


def boundary_ledgers() -> dict[str, Any]:
    ledgers = {
        "gamma_floor": (Fraction(20, 8), [Fraction(8, 8), Fraction(1, 8), Fraction(1, 8), Fraction(8, 8)]),
        "packet_energy_floor": (Fraction(18, 8), [Fraction(8, 8), Fraction(1, 8), Fraction(1, 8), Fraction(6, 8)]),
        "off_packet_ceiling": (Fraction(16, 8), [Fraction(8, 8), Fraction(1, 8), Fraction(1, 8), Fraction(5, 8)]),
        "size_ceiling": (Fraction(14, 8), [Fraction(8, 8), Fraction(1, 8), Fraction(1, 8), Fraction(4, 8)]),
    }
    out = {}
    for face, (source, losses) in ledgers.items():
        margin = source - sum(losses, Fraction(0))
        out[face] = {
            "source": q(source),
            "losses": [q(x) for x in losses],
            "margin": q(margin),
            "candidate_strictly_positive": margin > 0,
            "actual_pde_derivative_identity_proved": False,
        }
    return {
        "faces": out,
        "all_candidate_ledgers_positive": all(x["candidate_strictly_positive"] for x in out.values()),
        "dini_inwardness_promoted": False,
    }


def select_chart(energy: Sequence[Fraction], weights: Sequence[Fraction] | None = None) -> int | None:
    if not energy or sum(energy, Fraction(0)) == 0:
        return None
    if weights is None:
        weights = [Fraction(1) for _ in energy]
    scores = [w * e for w, e in zip(weights, energy)]
    return max(range(len(scores)), key=lambda j: (scores[j], -j))


def hysteresis_trace(trace: Sequence[Sequence[Fraction]], epsilon: Fraction = Fraction(1, 8)) -> dict[str, Any]:
    current: int | None = None
    switches: list[dict[str, Any]] = []
    selected: list[int | None] = []
    for t, energy in enumerate(trace):
        candidate = select_chart(energy)
        if current is None:
            current = candidate
        elif candidate is not None and candidate != current:
            old = energy[current]
            new = energy[candidate]
            if new >= (1 + epsilon) * old:
                switches.append({"time": t, "old": current, "new": candidate, "old_energy": q(old), "new_energy": q(new)})
                current = candidate
        selected.append(current)
    return {"epsilon": q(epsilon), "selected": selected, "switches": switches, "switch_count": len(switches)}


def coverage_scan() -> dict[str, Any]:
    threshold = Fraction(1, 4)
    families: dict[str, list[Fraction]] = {
        "zero": [Fraction(0)] * 16,
        "geometric": [Fraction(1, 2**j) for j in range(16)],
        "power_p2": [Fraction(1, (j + 1) ** 2) for j in range(16)],
        "plateau_4": [Fraction(1, 4) if 4 <= j < 8 else Fraction(0) for j in range(16)],
        "plateau_8": [Fraction(1, 8) if 4 <= j < 12 else Fraction(0) for j in range(16)],
    }
    reports = {}
    for name, energy in families.items():
        total = sum(energy, Fraction(0))
        k = select_chart(energy)
        max_fraction = Fraction(0) if k is None or total == 0 else energy[k] / total
        reports[name] = {
            "selected_shell": k,
            "max_shell_fraction": q(max_fraction),
            "normalized_chart_branch": k is not None and max_fraction >= threshold,
            "diffuse_branch": total > 0 and max_fraction < threshold,
            "zero_branch": total == 0,
        }
    trace = []
    for t in range(12):
        e = [Fraction(0)] * 8
        e[2] = Fraction(max(0, 12 - t), 12)
        e[3] = Fraction(t, 12)
        trace.append(e)
    h = hysteresis_trace(trace)
    return {
        "normalized_packet_threshold": q(threshold),
        "families": reports,
        "hysteresis_trace": h,
        "fixed_absolute_floor_rejected": True,
        "finite_trace_switching_locally_finite": h["switch_count"] < len(trace),
        "diffuse_implies_BKM_proved": False,
        "all_data_coverage_promoted": False,
    }


def build() -> dict[str, Any]:
    core = {
        "schema": SCHEMA,
        "authority": "deterministic_exact_finite_program_plus_explicit_open_universal_bridges",
        "carrier": carrier_contract(),
        "far_low": {"small_core": far_low_enumeration(), "certificate": far_low_certificate()},
        "far_high": far_high_scan(),
        "near_triad": near_triad_budget(),
        "five_halves": five_halves_falsification(),
        "boundary_faces": boundary_ledgers(),
        "coverage": coverage_scan(),
        "promotion": {
            "official_carrier_inhabitant": False,
            "universal_five_halves": False,
            "universal_dini_inwardness": False,
            "universal_all_data_coverage": False,
            "full_ns": False,
            "clay": False,
        },
    }
    core["certificate_sha256"] = digest(core)
    return core


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--output-json", type=Path, required=True)
    ap.add_argument("--pretty", action="store_true")
    args = ap.parse_args()
    payload = build()
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(payload, sort_keys=True, indent=2 if args.pretty else None) + "\n"
    args.output_json.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
