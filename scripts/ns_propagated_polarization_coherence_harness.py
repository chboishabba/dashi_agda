#!/usr/bin/env python3
"""Finite NS propagated-polarization coherence harness.

This is a local numerical diagnostic for the repaired finite NS theorem target.
It uses the exact finite Leray-vorticity bookkeeping from
``ns_exact_strain_eigenbundle.py`` and tests a stricter cascade condition than
the old Family-I/II output-only residual:

    (a, Omega_a), (b, Omega_b) -> (c, Omega_c)
    (c, Omega_c), (d, Omega_d) -> (e, Omega_e)

The second step must preserve the propagated output polarization as an
admissible next-step input and keep the transported vorticity/velocity/strain
frame coherent.  This is not a PDE proof, not a Clay proof, and not a theorem
promotion surface.
"""

from __future__ import annotations

import argparse
import json
import math
import random
import statistics
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable, Sequence


SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import ns_exact_strain_eigenbundle as exact_ns  # noqa: E402


Vec3 = exact_ns.Vec3
EPS = 1.0e-12


@dataclass(frozen=True)
class ResidualRecord:
    first_output_c: Vec3
    second_output_e: Vec3
    input_admissibility: float
    second_output_zero_mode: float
    omega_transport: float
    velocity_transport: float
    strain_plus_transport: float
    carry_velocity: float
    combined_max: float
    combined_rms: float


@dataclass(frozen=True)
class HarnessSummary:
    scope: str
    promotion: bool
    clay_promoted: bool
    seed: int
    samples: int
    attempts: int
    first_step_valid: int
    second_step_valid: int
    survivors: int
    survival_fraction_of_second_valid: float
    threshold: float
    transport_threshold: float
    width_first_outputs: float | None
    width_second_outputs: float | None
    width_survivor_first_outputs: float | None
    width_survivor_second_outputs: float | None
    residual_quantiles: dict[str, dict[str, float | None]]
    failure_counts: dict[str, int]
    worst_records: list[dict[str, object]]


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=20260608)
    parser.add_argument("--samples", type=int, default=4000)
    parser.add_argument("--threshold", type=float, default=0.04)
    parser.add_argument("--transport-threshold", type=float, default=0.12)
    parser.add_argument("--normals", type=int, default=512)
    parser.add_argument("--rho-min", type=float, default=0.6)
    parser.add_argument("--rho-max", type=float, default=1.6)
    parser.add_argument(
        "--input-mode",
        choices=("random", "canonical", "mixed"),
        default="random",
        help="How to choose first-generation input vorticities.",
    )
    parser.add_argument(
        "--second-input-mode",
        choices=("random", "canonical", "mixed"),
        default="random",
        help="How to choose the free second-generation input vorticity Omega_d.",
    )
    parser.add_argument("--show-worst", type=int, default=5)
    parser.add_argument("--json-output", type=Path, default=None)
    parser.add_argument("--json", action="store_true", help="Print JSON only.")
    return parser.parse_args(argv)


def dot(u: Vec3, v: Vec3) -> float:
    return exact_ns.dot(u, v)


def add(u: Vec3, v: Vec3) -> Vec3:
    return exact_ns.add(u, v)


def sub(u: Vec3, v: Vec3) -> Vec3:
    return exact_ns.sub(u, v)


def scale(s: float, u: Vec3) -> Vec3:
    return exact_ns.scale(s, u)


def norm(u: Vec3) -> float:
    return exact_ns.norm(u)


def normalize(u: Vec3) -> Vec3 | None:
    return exact_ns.normalize(u)


def project(k: Vec3, v: Vec3) -> Vec3 | None:
    return exact_ns.project_onto_plane(k, v)


def signless_line_residual(u: Vec3 | None, v: Vec3 | None) -> float:
    """Return 0 for equal/opposite unit lines and 1 for orthogonal/invalid."""

    if u is None or v is None:
        return 1.0
    u_hat = normalize(u)
    v_hat = normalize(v)
    if u_hat is None or v_hat is None:
        return 1.0
    return max(0.0, 1.0 - abs(dot(u_hat, v_hat)))


def perpendicular_residual(u: Vec3 | None, v: Vec3 | None) -> float:
    """Return 0 when u and v are perpendicular, 1 when aligned/invalid."""

    if u is None or v is None:
        return 1.0
    u_hat = normalize(u)
    v_hat = normalize(v)
    if u_hat is None or v_hat is None:
        return 1.0
    return abs(dot(u_hat, v_hat))


def random_unit(rng: random.Random) -> Vec3:
    z = rng.uniform(-1.0, 1.0)
    phi = rng.uniform(0.0, 2.0 * math.pi)
    r = math.sqrt(max(0.0, 1.0 - z * z))
    return (r * math.cos(phi), r * math.sin(phi), z)


def random_tangent_polarization(k: Vec3, rng: random.Random) -> Vec3 | None:
    basis = exact_ns.tangent_basis(k)
    if basis is None:
        return None
    angle = rng.uniform(0.0, 2.0 * math.pi)
    return normalize(add(scale(math.cos(angle), basis.e1), scale(math.sin(angle), basis.e2)))


def canonical_tangent_polarization(k: Vec3, salt: int = 0) -> Vec3 | None:
    models = ("e1", "e2", "plus45", "minus45")
    return exact_ns.vorticity_polarization(k, models[salt % len(models)])


def choose_polarization(k: Vec3, rng: random.Random, mode: str, salt: int = 0) -> Vec3 | None:
    if mode == "random":
        return random_tangent_polarization(k, rng)
    if mode == "canonical":
        return canonical_tangent_polarization(k, salt)
    if mode == "mixed":
        if rng.random() < 0.5:
            return canonical_tangent_polarization(k, salt)
        return random_tangent_polarization(k, rng)
    raise ValueError(f"unknown input mode: {mode}")


def sample_nonresonant_pair(rng: random.Random, rho_min: float, rho_max: float) -> tuple[Vec3, Vec3] | None:
    a = random_unit(rng)
    b_dir = random_unit(rng)
    rho = rng.uniform(rho_min, rho_max)
    b = scale(rho, b_dir)
    c = add(a, b)
    if norm(c) <= 1.0e-7:
        return None
    return a, b


def family_output_zero_residual(output_direction: Vec3, first_input: Vec3, second_input: Vec3, omega_output: Vec3) -> float:
    """Old output-only residual: included as one component, not sufficient alone."""

    projected_second = project(output_direction, second_input)
    projected_first = project(output_direction, first_input)
    family_i = signless_line_residual(omega_output, projected_second)
    family_ii = perpendicular_residual(omega_output, projected_first)
    return min(family_i, family_ii)


def next_input_admissibility_residual(c_hat: Vec3, d: Vec3, e_hat: Vec3, omega_c: Vec3) -> float:
    """Residual for propagated Omega_c as an admissible input to (c,d)->e.

    This is the repaired finite-target proxy: the carried polarization must not
    merely be tangent to c; it must align with one of the local interaction
    channels determined by the next input and output geometry.
    """

    channel_from_free_input = project(c_hat, d)
    channel_from_next_output = project(c_hat, e_hat)
    parallel_to_next_input = signless_line_residual(omega_c, channel_from_free_input)
    perpendicular_to_next_output = perpendicular_residual(omega_c, channel_from_next_output)
    return min(parallel_to_next_input, perpendicular_to_next_output)


def transported_line_residual(source_line: Vec3, source_base: Vec3, target_line: Vec3, target_base: Vec3) -> float:
    """Project a source tangent line into the target tangent plane and compare."""

    del source_base  # The bases are retained in the signature for readability.
    projected_source = project(target_base, source_line)
    return signless_line_residual(projected_source, target_line)


def estimate_width(points: list[Vec3], normals: list[Vec3]) -> float | None:
    if not points:
        return None
    best = 0.0
    for n in normals:
        strip_distance = min(abs(dot(n, p)) for p in points)
        if strip_distance > best:
            best = strip_distance
    return best


def quantiles(values: list[float]) -> dict[str, float | None]:
    if not values:
        return {"min": None, "median": None, "p90": None, "p95": None, "max": None}
    ordered = sorted(values)

    def pct(p: float) -> float:
        index = min(len(ordered) - 1, max(0, int(round(p * (len(ordered) - 1)))))
        return ordered[index]

    return {
        "min": ordered[0],
        "median": statistics.median(ordered),
        "p90": pct(0.90),
        "p95": pct(0.95),
        "max": ordered[-1],
    }


def rounded_vec(u: Vec3, digits: int = 8) -> list[float]:
    return [round(x, digits) for x in u]


def build_record(
    first: exact_ns.TriadicStrainEigenbundle,
    second: exact_ns.TriadicStrainEigenbundle,
) -> ResidualRecord:
    first_velocity = first.velocity
    second_velocity = second.velocity
    c_hat = first.strain.c_hat
    e_hat = second.strain.c_hat
    omega_c = first.strain.omega_out
    omega_e = second.strain.omega_out
    u_c_hat = first.strain.u_hat
    u_e_hat = second.strain.u_hat

    recovered_u_c = exact_ns.biot_savart_velocity(c_hat, omega_c)
    input_admissibility = next_input_admissibility_residual(
        c_hat,
        second_velocity.b,
        e_hat,
        omega_c,
    )
    second_output_zero_mode = family_output_zero_residual(
        e_hat,
        second_velocity.a,
        second_velocity.b,
        omega_e,
    )
    omega_transport = transported_line_residual(omega_c, c_hat, omega_e, e_hat)
    velocity_transport = transported_line_residual(u_c_hat, c_hat, u_e_hat, e_hat)
    strain_plus_transport = transported_line_residual(first.strain.e_plus, c_hat, second.strain.e_plus, e_hat)
    carry_velocity = signless_line_residual(u_c_hat, recovered_u_c)

    components = [
        input_admissibility,
        second_output_zero_mode,
        omega_transport,
        velocity_transport,
        strain_plus_transport,
        carry_velocity,
    ]
    combined_max = max(components)
    combined_rms = math.sqrt(sum(x * x for x in components) / len(components))
    return ResidualRecord(
        first_output_c=c_hat,
        second_output_e=e_hat,
        input_admissibility=input_admissibility,
        second_output_zero_mode=second_output_zero_mode,
        omega_transport=omega_transport,
        velocity_transport=velocity_transport,
        strain_plus_transport=strain_plus_transport,
        carry_velocity=carry_velocity,
        combined_max=combined_max,
        combined_rms=combined_rms,
    )


def run_harness(args: argparse.Namespace) -> HarnessSummary:
    rng = random.Random(args.seed)
    normals = [random_unit(rng) for _ in range(args.normals)]
    failure_counts = {
        "near_resonant_pair": 0,
        "omega_a_missing": 0,
        "omega_b_missing": 0,
        "first_step_degenerate": 0,
        "omega_d_missing": 0,
        "second_step_degenerate": 0,
    }
    first_outputs: list[Vec3] = []
    second_outputs: list[Vec3] = []
    survivor_first_outputs: list[Vec3] = []
    survivor_second_outputs: list[Vec3] = []
    records: list[ResidualRecord] = []
    first_step_valid = 0
    second_step_valid = 0
    survivors = 0
    attempts = 0

    for sample_index in range(args.samples):
        attempts += 1
        pair = sample_nonresonant_pair(rng, args.rho_min, args.rho_max)
        if pair is None:
            failure_counts["near_resonant_pair"] += 1
            continue
        a, b = pair
        omega_a = choose_polarization(a, rng, args.input_mode, 0)
        omega_b = choose_polarization(b, rng, args.input_mode, 1)
        if omega_a is None:
            failure_counts["omega_a_missing"] += 1
            continue
        if omega_b is None:
            failure_counts["omega_b_missing"] += 1
            continue

        first = exact_ns.triadic_strain_eigenbundle(a, b, omega_a, omega_b)
        if first is None:
            failure_counts["first_step_degenerate"] += 1
            continue
        first_step_valid += 1
        c_hat = first.strain.c_hat
        first_outputs.append(c_hat)

        d_dir = random_unit(rng)
        rho_d = rng.uniform(args.rho_min, args.rho_max)
        d = scale(rho_d, d_dir)
        omega_d = choose_polarization(d, rng, args.second_input_mode, sample_index + 17)
        if omega_d is None:
            failure_counts["omega_d_missing"] += 1
            continue

        second = exact_ns.triadic_strain_eigenbundle(c_hat, d, first.strain.omega_out, omega_d)
        if second is None:
            failure_counts["second_step_degenerate"] += 1
            continue
        second_step_valid += 1
        second_outputs.append(second.strain.c_hat)

        record = build_record(first, second)
        records.append(record)

        if (
            record.input_admissibility <= args.threshold
            and record.second_output_zero_mode <= args.threshold
            and record.omega_transport <= args.transport_threshold
            and record.velocity_transport <= args.transport_threshold
            and record.strain_plus_transport <= args.transport_threshold
            and record.carry_velocity <= args.threshold
        ):
            survivors += 1
            survivor_first_outputs.append(record.first_output_c)
            survivor_second_outputs.append(record.second_output_e)

    residual_fields = [
        "input_admissibility",
        "second_output_zero_mode",
        "omega_transport",
        "velocity_transport",
        "strain_plus_transport",
        "carry_velocity",
        "combined_max",
        "combined_rms",
    ]
    residual_quantiles = {
        field: quantiles([float(getattr(record, field)) for record in records])
        for field in residual_fields
    }
    worst = sorted(records, key=lambda record: record.combined_max, reverse=True)[: args.show_worst]
    worst_records = [
        {
            "first_output_c": rounded_vec(record.first_output_c),
            "second_output_e": rounded_vec(record.second_output_e),
            "input_admissibility": record.input_admissibility,
            "second_output_zero_mode": record.second_output_zero_mode,
            "omega_transport": record.omega_transport,
            "velocity_transport": record.velocity_transport,
            "strain_plus_transport": record.strain_plus_transport,
            "carry_velocity": record.carry_velocity,
            "combined_max": record.combined_max,
            "combined_rms": record.combined_rms,
        }
        for record in worst
    ]
    return HarnessSummary(
        scope="finite_leray_vorticity_propagated_polarization_diagnostic_not_pde_proof",
        promotion=False,
        clay_promoted=False,
        seed=args.seed,
        samples=args.samples,
        attempts=attempts,
        first_step_valid=first_step_valid,
        second_step_valid=second_step_valid,
        survivors=survivors,
        survival_fraction_of_second_valid=(survivors / second_step_valid if second_step_valid else 0.0),
        threshold=args.threshold,
        transport_threshold=args.transport_threshold,
        width_first_outputs=estimate_width(first_outputs, normals),
        width_second_outputs=estimate_width(second_outputs, normals),
        width_survivor_first_outputs=estimate_width(survivor_first_outputs, normals),
        width_survivor_second_outputs=estimate_width(survivor_second_outputs, normals),
        residual_quantiles=residual_quantiles,
        failure_counts=failure_counts,
        worst_records=worst_records,
    )


def emit_summary(summary: HarnessSummary, json_only: bool) -> None:
    payload = asdict(summary)
    if json_only:
        print(json.dumps(payload, indent=2, sort_keys=True))
        return
    print("NS propagated polarization coherence harness")
    print(f"  scope: {summary.scope}")
    print(f"  promotion: {summary.promotion}")
    print(f"  seed: {summary.seed}")
    print(f"  samples: {summary.samples}")
    print(f"  first_step_valid: {summary.first_step_valid}")
    print(f"  second_step_valid: {summary.second_step_valid}")
    print(f"  survivors: {summary.survivors}")
    print(f"  survival_fraction_of_second_valid: {summary.survival_fraction_of_second_valid:.6g}")
    print(f"  width_first_outputs: {summary.width_first_outputs}")
    print(f"  width_second_outputs: {summary.width_second_outputs}")
    print(f"  width_survivor_first_outputs: {summary.width_survivor_first_outputs}")
    print(f"  width_survivor_second_outputs: {summary.width_survivor_second_outputs}")
    print("  residual medians:")
    for key, stats in summary.residual_quantiles.items():
        print(f"    {key}: {stats['median']}")
    print("  failure_counts:")
    for key, value in summary.failure_counts.items():
        print(f"    {key}: {value}")


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    summary = run_harness(args)
    if args.json_output is not None:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        args.json_output.write_text(json.dumps(asdict(summary), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    emit_summary(summary, args.json)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
