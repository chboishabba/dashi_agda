#!/usr/bin/env python3
"""Exact/reconnaissance laboratory for the periodic Navier--Stokes Wall-I split.

This is deliberately not a proof of a cutoff-uniform PDE estimate.  It freezes one
finite Galerkin model, computes exact rational shell/kernel geometry, and runs
floating-point state experiments that can falsify proposed allocations.

Frozen conventions
------------------
* Torus: (R / 2*pi Z)^3.
* Fourier series: u(x) = sum_k u_hat(k) exp(i k.x), so d_j -> i k_j.
* Cutoff: max-coordinate cube |k|_infinity <= N.
* Zero mode: retained by the enumerator, but Biot--Savart is zero there.
* Coefficient norm: Euclidean norm on C^3.
* Leray: P_k = I - k tensor k / |k|_2^2 for k != 0; P_0 = I.
* Biot--Savart: i k cross / |k|_2^2 for k != 0; zero at k = 0.
* Shell radius: exact integer rho(k)=|k|_infinity.
* Shell multiplier: rational dyadic hat with centres 2^j and at most two
  simultaneously non-zero shells.  This is a proof-friendly surrogate for a
  smooth Euclidean radial partition.

Exact arithmetic uses fractions.Fraction.  Random state experiments use complex
floating point and are evidence only.  The output explicitly distinguishes both.
"""
from __future__ import annotations

import argparse
import csv
import json
import math
import random
from collections import defaultdict
from dataclasses import asdict, dataclass
from fractions import Fraction
from itertools import product
from pathlib import Path
from typing import DefaultDict, Dict, Iterator, List, Mapping, Sequence, Tuple

Mode = Tuple[int, int, int]
CVec = Tuple[complex, complex, complex]
QMatrix = Tuple[Tuple[Fraction, Fraction, Fraction], ...]

LANES = (
    "near-low-high",
    "near-high-low",
    "near-high-high",
    "far-low-left",
    "far-low-right",
    "far-high",
)


def mode_add(p: Mode, q: Mode) -> Mode:
    return (p[0] + q[0], p[1] + q[1], p[2] + q[2])


def mode_neg(k: Mode) -> Mode:
    return (-k[0], -k[1], -k[2])


def in_cutoff(k: Mode, cutoff: int) -> bool:
    return max(abs(k[0]), abs(k[1]), abs(k[2])) <= cutoff


def cube_modes(cutoff: int) -> List[Mode]:
    """Literal duplicate-free max-coordinate cube."""
    if cutoff < 0:
        raise ValueError("cutoff must be nonnegative")
    return list(product(range(-cutoff, cutoff + 1), repeat=3))


def rho(k: Mode) -> int:
    return max(abs(k[0]), abs(k[1]), abs(k[2]))


def norm2_sq(k: Mode) -> int:
    return k[0] * k[0] + k[1] * k[1] + k[2] * k[2]


def l1(k: Mode) -> int:
    return abs(k[0]) + abs(k[1]) + abs(k[2])


def dyadic_level_from_radius(r: int) -> int:
    """Band index with level 0 owning r in {0,1}."""
    if r <= 1:
        return 0
    return r.bit_length() - 1


def dyadic_level(k: Mode) -> int:
    return dyadic_level_from_radius(rho(k))


def hat_multiplier(shell: int, radius: int) -> Fraction:
    """Exact rational dyadic hat multiplier.

    shell=0 is the low cap: value 1 on radius <= 1 and decreases linearly to
    zero at radius 2.  For shell>=1 the support is
    [2^(j-1), 2^(j+1)] with value one at 2^j.
    """
    if shell < 0 or radius < 0:
        raise ValueError("shell and radius must be nonnegative")
    if shell == 0:
        if radius <= 1:
            return Fraction(1)
        if radius <= 2:
            return Fraction(2 - radius)
        return Fraction(0)
    lower = 1 << (shell - 1)
    centre = 1 << shell
    upper = 1 << (shell + 1)
    if radius < lower or radius > upper:
        return Fraction(0)
    if radius <= centre:
        return Fraction(radius - lower, centre - lower)
    return Fraction(upper - radius, upper - centre)


def shell_weights_at_radius(radius: int, max_shell: int | None = None) -> Dict[int, Fraction]:
    if max_shell is None:
        max_shell = max(1, dyadic_level_from_radius(radius) + 2)
    return {j: w for j in range(max_shell + 1) if (w := hat_multiplier(j, radius)) != 0}


def verify_shell_profile(max_radius: int) -> Dict[str, object]:
    worst_overlap = 0
    failures: List[Tuple[int, str]] = []
    for r in range(max_radius + 1):
        weights = shell_weights_at_radius(r)
        worst_overlap = max(worst_overlap, len(weights))
        if sum(weights.values(), Fraction(0)) != 1:
            failures.append((r, "partition"))
        if any(w < 0 or w > 1 for w in weights.values()):
            failures.append((r, "range"))
    return {
        "max_radius": max_radius,
        "worst_overlap": worst_overlap,
        "partition_exact": not failures,
        "failures": failures,
    }


def leray_matrix(k: Mode) -> QMatrix:
    n2 = norm2_sq(k)
    if n2 == 0:
        return tuple(tuple(Fraction(int(i == j)) for j in range(3)) for i in range(3))
    return tuple(
        tuple(Fraction(int(i == j)) - Fraction(k[i] * k[j], n2) for j in range(3))
        for i in range(3)
    )


def biot_savart_cross_matrix(k: Mode) -> QMatrix:
    """Real cross-product matrix divided by |k|^2; the Fourier operator has factor i."""
    n2 = norm2_sq(k)
    if n2 == 0:
        z = Fraction(0)
        return ((z, z, z), (z, z, z), (z, z, z))
    x, y, z = k
    raw = ((0, -z, y), (z, 0, -x), (-y, x, 0))
    return tuple(tuple(Fraction(raw[i][j], n2) for j in range(3)) for i in range(3))


def matrix_one_norm(matrix: QMatrix) -> Fraction:
    return max(sum(abs(matrix[i][j]) for i in range(3)) for j in range(3))


def multiplier_difference(shell: int, k: Mode, q: Mode) -> Fraction:
    return abs(hat_multiplier(shell, rho(k)) - hat_multiplier(shell, rho(q)))


def shell_distance(a: int, b: int) -> int:
    return abs(a - b)


def classify_triad(p: Mode, q: Mode, output_shell: int, separation: int, overlap: int) -> str:
    """Total deterministic split with oriented far-low placements."""
    lp = dyadic_level(p)
    lq = dyadic_level(q)
    if lp + separation <= output_shell and shell_distance(lq, output_shell) <= overlap:
        return "far-low-left"
    if lq + separation <= output_shell and shell_distance(lp, output_shell) <= overlap:
        return "far-low-right"
    if min(lp, lq) >= output_shell + separation:
        return "far-high"
    if lp + overlap < lq:
        return "near-low-high"
    if lq + overlap < lp:
        return "near-high-low"
    return "near-high-high"


def iter_target_triads(cutoff: int, output_shell: int) -> Iterator[Tuple[Mode, Mode, Mode]]:
    modes = cube_modes(cutoff)
    mode_set = set(modes)
    active_outputs = {k for k in modes if hat_multiplier(output_shell, rho(k)) != 0}
    for p in modes:
        for q in modes:
            k = mode_add(p, q)
            if k in mode_set and k in active_outputs:
                yield p, q, k


@dataclass
class TriadGeometryReport:
    cutoff: int
    output_shell: int
    separation: int
    overlap: int
    mode_count: int
    expected_mode_count: int
    active_output_count: int
    triad_count: int
    lane_counts: Dict[str, int]
    near_hilbert_schmidt_squared_max: Dict[str, str]
    near_hilbert_schmidt_bound_max: Dict[str, float]
    worst_near_output: Dict[str, Mode | None]


def triad_geometry_report(cutoff: int, output_shell: int, separation: int, overlap: int) -> TriadGeometryReport:
    modes = cube_modes(cutoff)
    lane_counts = {lane: 0 for lane in LANES}
    per_output_sq: Dict[str, DefaultDict[Mode, Fraction]] = {
        lane: defaultdict(Fraction) for lane in LANES if lane.startswith("near-")
    }
    active_outputs = {k for k in modes if hat_multiplier(output_shell, rho(k)) != 0}
    triad_count = 0
    for p, q, k in iter_target_triads(cutoff, output_shell):
        triad_count += 1
        lane = classify_triad(p, q, output_shell, separation, overlap)
        lane_counts[lane] += 1
        if lane.startswith("near-"):
            coefficient = (
                hat_multiplier(output_shell, rho(k))
                * matrix_one_norm(leray_matrix(k))
                * l1(q)
            )
            per_output_sq[lane][k] += coefficient * coefficient
    exact_max: Dict[str, str] = {}
    float_max: Dict[str, float] = {}
    worst_output: Dict[str, Mode | None] = {}
    for lane, rows in per_output_sq.items():
        if not rows:
            exact_max[lane] = "0"
            float_max[lane] = 0.0
            worst_output[lane] = None
            continue
        k_star, value = max(rows.items(), key=lambda item: item[1])
        exact_max[lane] = str(value)
        float_max[lane] = math.sqrt(float(value))
        worst_output[lane] = k_star
    return TriadGeometryReport(
        cutoff=cutoff,
        output_shell=output_shell,
        separation=separation,
        overlap=overlap,
        mode_count=len(modes),
        expected_mode_count=(2 * cutoff + 1) ** 3,
        active_output_count=len(active_outputs),
        triad_count=triad_count,
        lane_counts=lane_counts,
        near_hilbert_schmidt_squared_max=exact_max,
        near_hilbert_schmidt_bound_max=float_max,
        worst_near_output=worst_output,
    )


@dataclass
class SchurReport:
    row_count: int
    column_count: int
    nonzero_entries: int
    row_max: str
    row_argmax: Mode | None
    column_max: str
    column_argmax: Mode | None
    product: str
    product_float: float
    exact_complete: bool


def dyadic_weight(level: int, exponent: int) -> Fraction:
    power = exponent * level
    if power >= 0:
        return Fraction(1 << power)
    return Fraction(1, 1 << (-power))


def far_low_entry_majorant(p: Mode, q: Mode, k: Mode, output_shell: int, weight_exponent: int) -> Fraction:
    """Exact rational l1-majorant for one far-low commutator placement."""
    p_n2 = norm2_sq(p)
    if p_n2 == 0:
        return Fraction(0)
    diff = multiplier_difference(output_shell, k, q)
    if diff == 0:
        return Fraction(0)
    low_biot = Fraction(l1(p), p_n2)
    derivative = Fraction(l1(q))
    projection = matrix_one_norm(leray_matrix(k))
    input_level = max(0, dyadic_level(q))
    ratio = dyadic_weight(output_shell - input_level, weight_exponent)
    return diff * low_biot * derivative * projection * ratio


def far_low_schur_report(cutoff: int, output_shell: int, separation: int, overlap: int, weight_exponent: int, max_entries: int) -> SchurReport:
    rows: DefaultDict[Mode, Fraction] = defaultdict(Fraction)
    columns: DefaultDict[Mode, Fraction] = defaultdict(Fraction)
    nonzero = 0
    exact_complete = True
    for p, q, k in iter_target_triads(cutoff, output_shell):
        lane = classify_triad(p, q, output_shell, separation, overlap)
        if lane == "far-low-left":
            low, high = p, q
        elif lane == "far-low-right":
            low, high = q, p
        else:
            continue
        entry = far_low_entry_majorant(low, high, k, output_shell, weight_exponent)
        if entry == 0:
            continue
        nonzero += 1
        if nonzero > max_entries:
            exact_complete = False
            break
        rows[k] += entry
        columns[low] += entry
    if rows:
        row_argmax, row_max = max(rows.items(), key=lambda item: item[1])
    else:
        row_argmax, row_max = None, Fraction(0)
    if columns:
        col_argmax, col_max = max(columns.items(), key=lambda item: item[1])
    else:
        col_argmax, col_max = None, Fraction(0)
    product_value = row_max * col_max
    return SchurReport(
        row_count=len(rows),
        column_count=len(columns),
        nonzero_entries=nonzero,
        row_max=str(row_max),
        row_argmax=row_argmax,
        column_max=str(col_max),
        column_argmax=col_argmax,
        product=str(product_value),
        product_float=float(product_value),
        exact_complete=exact_complete,
    )


def geometric_tail_exact(start: int, surplus: int) -> Fraction:
    """sum_{n>=start} 2^{-surplus*n}, exact for positive integer surplus."""
    if start < 0 or surplus <= 0:
        raise ValueError("start must be nonnegative and surplus positive")
    first = Fraction(1, 1 << (surplus * start))
    ratio = Fraction(1, 1 << surplus)
    return first / (1 - ratio)


def far_high_tail_report(target_separation: int, sobolev_twice: int) -> Dict[str, object]:
    surplus_twice = sobolev_twice - 5
    report: Dict[str, object] = {
        "target_separation": target_separation,
        "sobolev_twice": sobolev_twice,
        "surplus_twice": surplus_twice,
    }
    if surplus_twice <= 0:
        report.update({"valid": False, "reason": "s - 5/2 is not positive"})
        return report
    if surplus_twice % 2:
        surplus = surplus_twice / 2.0
        ratio = 2.0 ** (-surplus)
        one = 2.0 ** (-surplus * target_separation) / (1.0 - ratio)
        report.update({
            "valid": True,
            "exact_rational": False,
            "one_placement": one,
            "two_placements": 2.0 * one,
            "fits_one_sixteenth": 2.0 * one <= 1.0 / 16.0,
            "fits_one_eighth": 2.0 * one <= 1.0 / 8.0,
        })
        return report
    surplus = surplus_twice // 2
    one_exact = geometric_tail_exact(target_separation, surplus)
    two_exact = 2 * one_exact
    report.update({
        "valid": True,
        "exact_rational": True,
        "one_placement": str(one_exact),
        "two_placements": str(two_exact),
        "one_placement_float": float(one_exact),
        "two_placements_float": float(two_exact),
        "fits_one_sixteenth": two_exact <= Fraction(1, 16),
        "fits_one_eighth": two_exact <= Fraction(1, 8),
    })
    return report


def cvec_add(a: CVec, b: CVec) -> CVec:
    return (a[0] + b[0], a[1] + b[1], a[2] + b[2])


def cvec_scale(z: complex, a: CVec) -> CVec:
    return (z * a[0], z * a[1], z * a[2])


def cvec_dot_real_mode(a: CVec, k: Mode) -> complex:
    return a[0] * k[0] + a[1] * k[1] + a[2] * k[2]


def cvec_inner(a: CVec, b: CVec) -> complex:
    return a[0].conjugate() * b[0] + a[1].conjugate() * b[1] + a[2].conjugate() * b[2]


def cvec_norm_sq(a: CVec) -> float:
    return float(cvec_inner(a, a).real)


def mat_vec_float(matrix: QMatrix, v: CVec) -> CVec:
    return tuple(sum(float(matrix[i][j]) * v[j] for j in range(3)) for i in range(3))  # type: ignore[return-value]


def project_divergence_free(k: Mode, v: CVec) -> CVec:
    return mat_vec_float(leray_matrix(k), v)


def random_state(modes: Sequence[Mode], rng: random.Random, amplitude: float, regularity: float, divergence_free: bool, real_symmetric: bool, shell: int | None) -> Dict[Mode, CVec]:
    state: Dict[Mode, CVec] = {}
    for k in sorted(modes):
        if real_symmetric and mode_neg(k) in state:
            partner = state[mode_neg(k)]
            state[k] = tuple(z.conjugate() for z in partner)  # type: ignore[assignment]
            continue
        if shell is not None and hat_multiplier(shell, rho(k)) == 0:
            state[k] = (0j, 0j, 0j)
            continue
        decay = (1.0 + norm2_sq(k)) ** (-0.5 * regularity)
        v: CVec = tuple(
            complex(rng.gauss(0.0, 1.0), rng.gauss(0.0, 1.0)) * amplitude * decay
            for _ in range(3)
        )  # type: ignore[assignment]
        if divergence_free and norm2_sq(k) != 0:
            v = project_divergence_free(k, v)
        if k == (0, 0, 0):
            v = (0j, 0j, 0j)
        state[k] = v
    return state


def lane_trilinear_and_dissipation(state: Mapping[Mode, CVec], cutoff: int, output_shell: int, separation: int, overlap: int, viscosity: float) -> Tuple[Dict[str, float], float]:
    modes = list(state)
    mode_set = set(modes)
    by_lane: Dict[str, Dict[Mode, CVec]] = {
        lane: {k: (0j, 0j, 0j) for k in modes} for lane in LANES
    }
    for p in modes:
        up = state[p]
        if cvec_norm_sq(up) == 0:
            continue
        for q in modes:
            k = mode_add(p, q)
            if k not in mode_set or hat_multiplier(output_shell, rho(k)) == 0:
                continue
            uq = state[q]
            if cvec_norm_sq(uq) == 0:
                continue
            scalar = cvec_dot_real_mode(up, q)
            raw = cvec_scale(-1j * scalar, uq)
            projected = mat_vec_float(leray_matrix(k), raw)
            lane = classify_triad(p, q, output_shell, separation, overlap)
            by_lane[lane][k] = cvec_add(by_lane[lane][k], projected)
    tested: Dict[str, float] = {}
    for lane in LANES:
        value = 0.0
        for k in modes:
            weight = float(hat_multiplier(output_shell, rho(k))) ** 2
            value += weight * cvec_inner(state[k], by_lane[lane][k]).real
        tested[lane] = abs(value)
    dissipation = 0.0
    for k in modes:
        weight = float(hat_multiplier(output_shell, rho(k))) ** 2
        dissipation += viscosity * norm2_sq(k) * weight * cvec_norm_sq(state[k])
    return tested, dissipation


def state_experiment(cutoff: int, output_shell: int, separation: int, overlap: int, viscosity: float, trials: int, seed: int) -> Dict[str, object]:
    modes = cube_modes(cutoff)
    rng = random.Random(seed)
    configurations = [
        ("arbitrary", False, False, None),
        ("divergence-free", True, False, None),
        ("real-divergence-free", True, True, None),
        ("shell-concentrated", True, True, output_shell),
    ]
    scales = (0.25, 0.5, 1.0, 2.0)
    output: Dict[str, object] = {}
    for name, div_free, real_sym, shell in configurations:
        rows: List[Dict[str, object]] = []
        for trial in range(trials):
            base = random_state(modes, rng, 1.0, 3.5, div_free, real_sym, shell)
            for scale in scales:
                state = {k: cvec_scale(scale, v) for k, v in base.items()}
                lane_values, dissipation = lane_trilinear_and_dissipation(
                    state, cutoff, output_shell, separation, overlap, viscosity
                )
                ratios = {
                    lane: (lane_values[lane] / dissipation if dissipation > 0 else math.inf)
                    for lane in LANES
                }
                rows.append({
                    "trial": trial,
                    "amplitude": scale,
                    "dissipation": dissipation,
                    "lane_values": lane_values,
                    "ratios": ratios,
                })
        output[name] = rows
    return output


def summarize_scale_homogeneity(experiments: Mapping[str, object]) -> Dict[str, object]:
    summary: Dict[str, object] = {}
    for name, raw_rows in experiments.items():
        rows = raw_rows if isinstance(raw_rows, list) else []
        by_lane: Dict[str, List[float]] = {lane: [] for lane in LANES}
        grouped: DefaultDict[Tuple[int, str], Dict[float, float]] = defaultdict(dict)
        for row in rows:
            if not isinstance(row, dict):
                continue
            trial = int(row["trial"])
            amplitude = float(row["amplitude"])
            ratios = row["ratios"]
            if not isinstance(ratios, dict):
                continue
            for lane in LANES:
                grouped[(trial, lane)][amplitude] = float(ratios[lane])
        for (trial, lane), values in grouped.items():
            if 1.0 in values and 2.0 in values and values[1.0] > 1e-15:
                by_lane[lane].append(values[2.0] / values[1.0])
        summary[name] = {
            lane: (sum(vals) / len(vals) if vals else None) for lane, vals in by_lane.items()
        }
    return summary


def write_csv_reports(prefix: Path, triad: TriadGeometryReport, schur: SchurReport) -> None:
    prefix.parent.mkdir(parents=True, exist_ok=True)
    with prefix.with_name(prefix.name + "_lane_counts.csv").open("w", newline="") as handle:
        writer = csv.writer(handle)
        writer.writerow(["lane", "count", "hs_squared", "hs_bound", "worst_output"])
        for lane in LANES:
            writer.writerow([
                lane,
                triad.lane_counts.get(lane, 0),
                triad.near_hilbert_schmidt_squared_max.get(lane, ""),
                triad.near_hilbert_schmidt_bound_max.get(lane, ""),
                triad.worst_near_output.get(lane, ""),
            ])
    with prefix.with_name(prefix.name + "_schur.csv").open("w", newline="") as handle:
        writer = csv.writer(handle)
        writer.writerow([
            "row_count", "column_count", "nonzero_entries", "row_max", "row_argmax",
            "column_max", "column_argmax", "product", "product_float", "exact_complete",
        ])
        writer.writerow([
            schur.row_count, schur.column_count, schur.nonzero_entries,
            schur.row_max, schur.row_argmax, schur.column_max, schur.column_argmax,
            schur.product, schur.product_float, schur.exact_complete,
        ])


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cutoff", type=int, default=3)
    parser.add_argument("--output-shell", type=int, default=1)
    parser.add_argument("--separation", type=int, default=2, help="finite-enumerator separation")
    parser.add_argument("--target-separation", type=int, default=8, help="analytic tail target")
    parser.add_argument("--overlap", type=int, default=1)
    parser.add_argument("--weight-exponent", type=int, default=1)
    parser.add_argument("--sobolev-twice", type=int, default=7, help="twice Sobolev index s")
    parser.add_argument("--viscosity", type=float, default=1.0)
    parser.add_argument("--random-trials", type=int, default=1)
    parser.add_argument("--seed", type=int, default=20260725)
    parser.add_argument("--max-schur-entries", type=int, default=2_000_000)
    parser.add_argument("--skip-state-experiments", action="store_true")
    parser.add_argument("--json-out", type=Path)
    parser.add_argument("--csv-prefix", type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.cutoff < 0 or args.output_shell < 0 or args.separation < 0:
        raise SystemExit("cutoff, output shell and separation must be nonnegative")
    shell_report = verify_shell_profile(max_radius=max(2, args.cutoff))
    triad_report = triad_geometry_report(args.cutoff, args.output_shell, args.separation, args.overlap)
    schur_report = far_low_schur_report(
        args.cutoff, args.output_shell, args.separation, args.overlap,
        args.weight_exponent, args.max_schur_entries,
    )
    high_report = far_high_tail_report(args.target_separation, args.sobolev_twice)
    experiments: Dict[str, object] = {}
    homogeneity: Dict[str, object] = {}
    if not args.skip_state_experiments and args.random_trials > 0:
        experiments = state_experiment(
            args.cutoff, args.output_shell, args.separation, args.overlap,
            args.viscosity, args.random_trials, args.seed,
        )
        homogeneity = summarize_scale_homogeneity(experiments)

    findings: List[str] = []
    if shell_report["partition_exact"] and shell_report["worst_overlap"] <= 2:
        findings.append("The rational shell profile is an exact bounded partition with overlap at most two on the tested radius range.")
    if high_report.get("valid"):
        findings.append("The far-high geometric factor is reported from s-5/2 and R; no target constant is imposed by hand.")
    if homogeneity:
        findings.append("Amplitude doubling diagnoses cubic nonlinear versus quadratic dissipative scaling; ratios near two rule out an amplitude-uniform epsilon-D estimate without an admissibility smallness parameter.")
    if not schur_report.exact_complete:
        findings.append("The exact Schur enumeration hit the configured entry cap; this run is incomplete.")
    findings.append("Finite cutoff output is a falsification/reconnaissance certificate only; cutoff-uniform claims require symbolic lattice sums and Agda proofs.")

    payload = {
        "status": "research-certificate-not-proof",
        "conventions": {
            "torus": "(R / 2*pi Z)^3",
            "fourier": "exp(i k.x)",
            "cutoff": "|k|_infinity <= N",
            "shell_radius": "|k|_infinity",
            "shell_profile": "exact rational dyadic hat",
            "zero_mode": "enumerated; Biot-Savart zero",
            "coefficient_norm": "Euclidean C^3",
        },
        "shell": shell_report,
        "triads": asdict(triad_report),
        "far_low_schur": asdict(schur_report),
        "far_high_tail": high_report,
        "state_experiments": experiments,
        "amplitude_doubling_ratio": homogeneity,
        "findings": findings,
    }
    text = json.dumps(payload, indent=2, sort_keys=True, default=list)
    print(text)
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(text + "\n", encoding="utf-8")
    if args.csv_prefix:
        write_csv_reports(args.csv_prefix, triad_report, schur_report)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
