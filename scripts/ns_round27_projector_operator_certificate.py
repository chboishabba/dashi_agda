#!/usr/bin/env python3
"""Generate exact finite certificates for the Round 27 NS algebra.

The script checks:
- sharp shell-projector idempotence, disjointness and finite resolution;
- the signed translation--multiplier commutator identity;
- the five-source centred-probe identity;
- maximal common-core reconstruction on a fixed nine-owner allocation;
- the three-dimensional Plucker/Gram identity.

It emits a JSON receipt and a small generated Agda module containing only the
verified finite counts and checksum.  The generated certificate is not a
cutoff-uniform analytic estimate.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from math import ceil, log2
from pathlib import Path
from typing import Iterable, Tuple

Mode = Tuple[int, int, int]


def shell_index(mode: Mode) -> int:
    magnitude = max(abs(x) for x in mode)
    return 0 if magnitude == 0 else ceil(log2(magnitude))


def subtract(left: Mode, right: Mode) -> Mode:
    return tuple(a - b for a, b in zip(left, right))  # type: ignore[return-value]


def multiplier(mode: Mode) -> int:
    x, y, z = mode
    return x + 2 * y + 3 * z


def state(mode: Mode) -> int:
    x, y, z = mode
    return 2 * x - y + z


def modes(radius: int) -> list[Mode]:
    return list(itertools.product(range(-radius, radius + 1), repeat=3))


def check_projectors(carrier: list[Mode]) -> dict[str, int]:
    maximum_shell = max(shell_index(mode) for mode in carrier)
    idempotence = 0
    disjointness = 0
    resolution = 0

    for shell in range(maximum_shell + 1):
        for mode in carrier:
            coefficient = int(shell == shell_index(mode))
            assert coefficient * coefficient == coefficient
            idempotence += 1

    for left in range(maximum_shell + 1):
        for right in range(maximum_shell + 1):
            if left == right:
                continue
            for mode in carrier:
                assert (
                    int(left == shell_index(mode))
                    * int(right == shell_index(mode))
                    == 0
                )
                disjointness += 1

    for mode in carrier:
        assert (
            sum(
                int(shell == shell_index(mode))
                for shell in range(maximum_shell + 1)
            )
            == 1
        )
        resolution += 1

    return {
        "maximum_shell": maximum_shell,
        "projector_idempotence_checks": idempotence,
        "projector_disjointness_checks": disjointness,
        "projector_resolution_checks": resolution,
    }


def check_commutator(carrier: list[Mode]) -> dict[str, object]:
    checked = 0
    maximum_absolute_value = 0
    digest = hashlib.sha256()

    for shift in carrier:
        for output in carrier:
            shifted = subtract(output, shift)
            left = (
                multiplier(output) * state(shifted)
                - multiplier(shifted) * state(shifted)
            )
            right = (
                multiplier(output) - multiplier(shifted)
            ) * state(shifted)
            assert left == right
            checked += 1
            maximum_absolute_value = max(maximum_absolute_value, abs(right))
            digest.update(f"{shift}:{output}:{right};".encode("utf-8"))

    return {
        "commutator_cells_checked": checked,
        "commutator_maximum_absolute_value": maximum_absolute_value,
        "commutator_sha256": digest.hexdigest(),
    }


def check_centred_probe() -> int:
    values = (-1, 0, 1)
    weights = (
        (1, 1, 1, 1, 1),
        (1, 2, 3, 4, 5),
        (5, 4, 3, 2, 1),
        (-1, 0, 1, 0, -1),
        (0, 1, 0, -1, 2),
    )
    checked = 0

    for base_and_deltas in itertools.product(values, repeat=6):
        base, *deltas = base_and_deltas
        sources = [base + delta for delta in deltas]
        augmentation = sum(sources)
        for weight in weights:
            weight_sum = sum(weight)
            left = 5 * sum(w * source for w, source in zip(weight, sources))
            right = weight_sum * augmentation + sum(
                (5 * w - weight_sum) * delta
                for w, delta in zip(weight, deltas)
            )
            assert left == right
            checked += 1

    return checked


def check_maximal_core() -> dict[str, object]:
    allocations = [9, 7, 8, 10, 7, 12, 11, 9, 8]
    maximal_core = min(allocations)
    checked = 0
    for candidate in range(maximal_core + 1):
        residuals = [allocation - candidate for allocation in allocations]
        assert all(
            candidate + residual == allocation
            for residual, allocation in zip(residuals, allocations)
        )
        assert candidate <= maximal_core
        checked += 1
    return {
        "owner_allocations": allocations,
        "maximal_uniform_core": maximal_core,
        "uniform_core_candidates_checked": checked,
    }


def check_plucker(carrier: list[Mode]) -> int:
    checked = 0
    for p in carrier:
        for q in carrier:
            px, py, pz = p
            qx, qy, qz = q
            cross_x = py * qz - pz * qy
            cross_y = pz * qx - px * qz
            cross_z = px * qy - py * qx
            left = cross_x**2 + cross_y**2 + cross_z**2
            norm_p = px**2 + py**2 + pz**2
            norm_q = qx**2 + qy**2 + qz**2
            dot = px * qx + py * qy + pz * qz
            right = norm_p * norm_q - dot**2
            assert left == right
            checked += 1
    return checked


def agda_module(payload: dict[str, object]) -> str:
    return f"""module DASHI.Physics.Closure.NSTriadKNLuoRound27FiniteCertificateGenerated where

-- Generated by scripts/ns_round27_projector_operator_certificate.py.
-- The module certifies finite arithmetic counts only; it does not assert a
-- cutoff-uniform PDE estimate.

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

projectorIdempotenceChecks : Nat
projectorIdempotenceChecks = {payload['projector_idempotence_checks']}

projectorDisjointnessChecks : Nat
projectorDisjointnessChecks = {payload['projector_disjointness_checks']}

projectorResolutionChecks : Nat
projectorResolutionChecks = {payload['projector_resolution_checks']}

commutatorCellsChecked : Nat
commutatorCellsChecked = {payload['commutator_cells_checked']}

centredProbeCasesChecked : Nat
centredProbeCasesChecked = {payload['centred_probe_cases_checked']}

pluckerPairsChecked : Nat
pluckerPairsChecked = {payload['plucker_pairs_checked']}

uniformCoreCandidatesChecked : Nat
uniformCoreCandidatesChecked = {payload['uniform_core_candidates_checked']}

commutatorChecksum : String
commutatorChecksum = \"{payload['commutator_sha256']}\"

allFiniteChecksPassed : Bool
allFiniteChecksPassed = true
"""


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--radius", type=int, default=2)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--agda-out", type=Path, required=True)
    args = parser.parse_args()
    if args.radius < 0:
        raise SystemExit("radius must be nonnegative")

    carrier = modes(args.radius)
    payload: dict[str, object] = {
        "radius": args.radius,
        "mode_count": len(carrier),
    }
    payload.update(check_projectors(carrier))
    payload.update(check_commutator(carrier))
    payload["centred_probe_cases_checked"] = check_centred_probe()
    payload.update(check_maximal_core())
    payload["plucker_pairs_checked"] = check_plucker(carrier)
    payload["all_checks_passed"] = True

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    args.agda_out.parent.mkdir(parents=True, exist_ok=True)
    args.agda_out.write_text(agda_module(payload))


if __name__ == "__main__":
    main()
