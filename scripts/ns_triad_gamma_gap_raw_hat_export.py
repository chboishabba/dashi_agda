#!/usr/bin/env python3
"""Export saved finite-Galerkin ``raw_hat`` states to the Gamma-gap JSON form.

This is the physical bridge for the canonical Gamma-gap audit.  Unlike the
existing raw-archive adapter, it evaluates the Leray-projected Fourier
convection term directly from saved complex velocity coefficients.  The output
is still a finite, frozen-phase/polarisation carrier: varying its probability
profile varies modal magnitudes while holding the observed directions/phases
fixed.  It is empirical discovery data, never theorem authority.

The current audit schema requires three distinct mode indices per triad.  A
physical repeated-input interaction ``p = q`` is consequently omitted and its
signed packet contribution is recorded explicitly in the receipt.
"""

from __future__ import annotations

import argparse
import heapq
import json
import math
import os
from pathlib import Path
import tempfile
from typing import Any

import numpy as np


SCRIPT_NAME = "scripts/ns_triad_gamma_gap_raw_hat_export.py"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--state", type=Path, action="append", required=True,
                        help="saved normalized-profile raw_hat NPZ; may be repeated in time order")
    parser.add_argument("--target-shell", type=int, default=2)
    parser.add_argument("--max-mode-pairs", type=int, default=48,
                        help="maximum reality-paired modes in the finite carrier")
    parser.add_argument("--target-mode-pairs", type=int, default=24,
                        help="minimum selected reality-pairs from the target shell")
    parser.add_argument("--selection", choices=("transfer", "energy"), default="transfer",
                        help="carrier selector; transfer ranks exact packet-transfer atoms")
    parser.add_argument("--transfer-seed-count", type=int, default=512,
                        help="number of global exact transfer atoms retained while building the carrier")
    parser.add_argument("--transfer-rank-counts", default="1,8,64,512,2048,8192",
                        help="comma-separated top-atom ranks reported in the gross-activity capture curve")
    parser.add_argument("--trajectory-id", default="N32-positive-chi-attempt1")
    parser.add_argument("--duration-c", type=float, default=None,
                        help="parabolic-window fraction per saved segment; defaults to segment_window_c")
    parser.add_argument("--output-json", type=Path, required=True)
    return parser.parse_args()


def atomic_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        mode="w", encoding="utf-8", dir=path.parent,
        prefix=f".{path.name}.", suffix=".partial", delete=False,
    ) as handle:
        temporary = Path(handle.name)
        json.dump(payload, handle, indent=2, sort_keys=True)
        handle.write("\n")
        handle.flush()
        os.fsync(handle.fileno())
    try:
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()


def frequency_data(n: int) -> tuple[np.ndarray, np.ndarray, np.ndarray, list[tuple[int, int, int]]]:
    axis = np.fft.fftfreq(n) * n
    kz, ky, kx = np.meshgrid(axis, axis, axis, indexing="ij")
    wave = np.stack((kx, ky, kz), axis=0)
    norm_sq = np.sum(wave * wave, axis=0)
    norm = np.sqrt(norm_sq)
    signed = [(int(kx[z, y, x]), int(ky[z, y, x]), int(kz[z, y, x]))
              for z, y, x in np.ndindex((n, n, n))]
    return wave, norm, norm_sq, signed


def index_of(mode: tuple[int, int, int], n: int) -> tuple[int, int, int]:
    x, y, z = mode
    return z % n, y % n, x % n


def negate(mode: tuple[int, int, int]) -> tuple[int, int, int]:
    return -mode[0], -mode[1], -mode[2]


def representative(mode: tuple[int, int, int]) -> tuple[int, int, int]:
    return min(mode, negate(mode))


def packet_mask(norm: np.ndarray, shell: int) -> np.ndarray:
    return (norm >= float(2 ** shell)) & (norm < float(2 ** (shell + 1)))


def dyadic_shell(vector_norm: np.ndarray) -> np.ndarray:
    """Return a finite dyadic shell label, with zero excluded by callers."""
    return np.floor(np.log2(np.maximum(vector_norm, 1.0))).astype(np.int64)


def coefficient_at(field: np.ndarray, mode: tuple[int, int, int]) -> np.ndarray:
    """Return one vector Fourier coefficient without NumPy tuple-index ambiguity."""
    n = int(field.shape[1])
    z, y, x = index_of(mode, n)
    return field[:, z, y, x]


def leray(vector: np.ndarray, k: np.ndarray) -> np.ndarray:
    norm_sq = float(np.dot(k, k))
    if norm_sq == 0.0:
        return np.zeros(3, dtype=np.complex128)
    return vector - k * (np.dot(k, vector) / norm_sq)


def select_modes(field: np.ndarray, norm: np.ndarray, dealias: np.ndarray,
                 signed: list[tuple[int, int, int]], target_shell: int,
                 max_pairs: int, target_pairs: int) -> list[tuple[int, int, int]]:
    energy = np.sum(np.abs(field) ** 2, axis=0).ravel()
    target = packet_mask(norm, target_shell).ravel()
    seen: set[tuple[int, int, int]] = set()
    target_reps: list[tuple[float, tuple[int, int, int]]] = []
    other_reps: list[tuple[float, tuple[int, int, int]]] = []
    for flat, mode in enumerate(signed):
        if mode == (0, 0, 0) or not bool(dealias.ravel()[flat]):
            continue
        rep = representative(mode)
        if rep in seen:
            continue
        seen.add(rep)
        row = (float(energy[flat] + energy[np.ravel_multi_index(
            index_of(negate(mode), int(norm.shape[0])), norm.shape
        )]), rep)
        (target_reps if bool(target[flat]) else other_reps).append(row)
    target_reps.sort(reverse=True)
    other_reps.sort(reverse=True)
    chosen = [rep for _, rep in target_reps[:target_pairs]]
    chosen_set = set(chosen)
    for _, rep in target_reps[target_pairs:] + other_reps:
        if len(chosen) >= max_pairs:
            break
        if rep not in chosen_set:
            chosen.append(rep)
            chosen_set.add(rep)
    modes: list[tuple[int, int, int]] = []
    for rep in chosen:
        modes.extend((rep, negate(rep)))
    return modes


def transfer_ranked_modes(
    field: np.ndarray,
    wave: np.ndarray,
    norm: np.ndarray,
    dealias: np.ndarray,
    target_shell: int,
    max_pairs: int,
    seed_count: int,
    rank_counts: tuple[int, ...],
) -> tuple[list[tuple[int, int, int]], dict[str, float | int]]:
    """Build a reality-closed carrier from exact full packet-transfer atoms.

    We enumerate all dealiased Galerkin pairs ``p + q = k`` for target packet
    outputs before choosing any carrier modes.  This is deliberately different
    from selecting energetic modes: every retained seed contributes a large
    observed packet transfer and brings its output/input partners with it.
    """
    n = int(field.shape[1])
    packet = packet_mask(norm, target_shell) & dealias
    all_modes = np.argwhere(dealias & (norm > 0.0))
    # Coordinates and coefficients use x,y,z order; array indices are z,y,x.
    p_modes = np.stack((
        wave[0][dealias & (norm > 0.0)],
        wave[1][dealias & (norm > 0.0)],
        wave[2][dealias & (norm > 0.0)],
    ), axis=1).astype(np.int64)
    p_coeff = field[:, all_modes[:, 0], all_modes[:, 1], all_modes[:, 2]].T
    cutoff = n // 3
    heap: list[tuple[float, int, tuple[int, int, int], tuple[int, int, int], tuple[int, int, int], float]] = []
    sequence = 0
    full_rate = 0.0
    full_gross = 0.0
    repeated_rate = 0.0
    repeated_gross = 0.0
    coarse_groups: dict[tuple[int, int, int], dict[str, float | int]] = {}

    for z, y, x in np.argwhere(packet):
        k_mode = np.asarray((wave[0, z, y, x], wave[1, z, y, x], wave[2, z, y, x]), dtype=np.int64)
        q_modes = k_mode[None, :] - p_modes
        valid = np.all(np.abs(q_modes) <= cutoff, axis=1) & np.any(q_modes != 0, axis=1)
        if not np.any(valid):
            continue
        p = p_modes[valid]
        q = q_modes[valid]
        up = p_coeff[valid]
        qz, qy, qx = q[:, 2] % n, q[:, 1] % n, q[:, 0] % n
        uq = field[:, qz, qy, qx].T
        dot_q_up = np.einsum("ij,ij->i", q.astype(np.float64), up)
        forcing = -1j * dot_q_up[:, None] * uq
        k_float = k_mode.astype(np.float64)
        forcing -= k_float[None, :] * (
            np.einsum("j,ij->i", k_float, forcing) / float(np.dot(k_float, k_float))
        )[:, None]
        transfer = 2.0 * (2 ** target_shell) * np.real(np.einsum("j,ij->i", np.conjugate(field[:, z, y, x]), forcing))
        full_rate += float(np.sum(transfer))
        full_gross += float(np.sum(np.abs(transfer)))
        p_norm = np.linalg.norm(p, axis=1)
        q_norm = np.linalg.norm(q, axis=1)
        dot_pq = np.einsum("ij,ij->i", p, q)
        cosine = np.clip(dot_pq / np.maximum(p_norm * q_norm, 1.0), -1.0, 1.0)
        p_shell = dyadic_shell(p_norm) - target_shell
        q_shell = dyadic_shell(q_norm) - target_shell
        angle_bin = np.minimum(11, np.maximum(0, ((cosine + 1.0) * 6.0).astype(np.int64)))
        for local, value in enumerate(transfer):
            group_key = (int(p_shell[local]), int(q_shell[local]), int(angle_bin[local]))
            group = coarse_groups.setdefault(group_key, {"signed_rate": 0.0, "gross_activity": 0.0, "atom_count": 0})
            group["signed_rate"] = float(group["signed_rate"]) + float(value)
            group["gross_activity"] = float(group["gross_activity"]) + abs(float(value))
            group["atom_count"] = int(group["atom_count"]) + 1
        repeated = np.all(p == q, axis=1)
        repeated_rate += float(np.sum(transfer[repeated]))
        repeated_gross += float(np.sum(np.abs(transfer[repeated])))
        for local in np.flatnonzero(~repeated):
            absolute = float(abs(transfer[local]))
            if absolute == 0.0:
                continue
            entry = (absolute, sequence, tuple(int(v) for v in k_mode),
                     tuple(int(v) for v in p[local]), tuple(int(v) for v in q[local]),
                     float(transfer[local]))
            sequence += 1
            if len(heap) < seed_count:
                heapq.heappush(heap, entry)
            elif absolute > heap[0][0]:
                heapq.heapreplace(heap, entry)

    ordered = sorted(heap, reverse=True)
    capture_curve: list[dict[str, float | int]] = []
    running_gross = 0.0
    requested = set(rank_counts)
    for rank, entry in enumerate(ordered, start=1):
        running_gross += entry[0]
        if rank in requested:
            capture_curve.append({
                "rank": rank,
                "gross_activity": running_gross,
                "gross_activity_fraction": running_gross / full_gross if full_gross > 0.0 else 0.0,
            })
    for rank in rank_counts:
        if rank > len(ordered):
            capture_curve.append({
                "rank": rank,
                "gross_activity": running_gross,
                "gross_activity_fraction": running_gross / full_gross if full_gross > 0.0 else 0.0,
                "lower_bound": True,
            })
    coarse_receipt = [
        {
            "p_shell_offset": key[0], "q_shell_offset": key[1], "angle_bin": key[2],
            "signed_rate": float(value["signed_rate"]),
            "gross_activity": float(value["gross_activity"]),
            "gross_activity_fraction": float(value["gross_activity"]) / full_gross if full_gross > 0.0 else 0.0,
            "atom_count": int(value["atom_count"]),
        }
        for key, value in sorted(coarse_groups.items(), key=lambda item: float(item[1]["gross_activity"]), reverse=True)
    ]
    chosen_reps: set[tuple[int, int, int]] = set()
    accepted = 0
    accepted_seed_gross = 0.0
    accepted_seed_rate = 0.0
    for _absolute, _sequence, k_mode, p_mode, q_mode, _transfer in ordered:
        new_reps = {representative(k_mode), representative(p_mode), representative(q_mode)}
        if len(chosen_reps | new_reps) > max_pairs:
            continue
        chosen_reps |= new_reps
        accepted += 1
        accepted_seed_gross += _absolute
        accepted_seed_rate += _transfer
    modes: list[tuple[int, int, int]] = []
    for rep in sorted(chosen_reps):
        modes.extend((rep, negate(rep)))
    if not modes:
        raise ValueError("transfer-ranked selection found no nonrepeated target packet atoms")
    return modes, {
        "full_packet_signed_rate": full_rate,
        "full_packet_gross_activity": full_gross,
        "full_repeated_input_signed_rate": repeated_rate,
        "full_repeated_input_gross_activity": repeated_gross,
        "transfer_seed_count_considered": len(ordered),
        "transfer_seed_count_accepted": accepted,
        "accepted_seed_gross_activity": accepted_seed_gross,
        "accepted_seed_signed_rate": accepted_seed_rate,
        "top_atom_gross_capture_curve": sorted(capture_curve, key=lambda point: int(point["rank"])),
        "coarse_shell_angle_groups": coarse_receipt,
    }


def export_problem(state_path: Path, time: float, duration: float, target_shell: int,
                   max_pairs: int, target_pairs: int, selection: str,
                   transfer_seed_count: int, rank_counts: tuple[int, ...],
                   trajectory_id: str) -> tuple[dict[str, Any], dict[str, Any]]:
    with np.load(state_path, allow_pickle=False) as data:
        raw = np.asarray(data["raw_hat"], dtype=np.complex128)
        nu = float(data["nu"]) if "nu" in data else 1.0e-3
    if raw.ndim != 4 or raw.shape[-1] != 3 or len(set(raw.shape[:3])) != 1:
        raise ValueError(f"{state_path}: expected raw_hat shape (N,N,N,3), got {raw.shape!r}")
    n = int(raw.shape[0])
    field = np.moveaxis(raw / float(n ** 3), -1, 0)
    wave, norm, _norm_sq, signed = frequency_data(n)
    dealias = np.all(np.abs(wave) <= float(n) / 3.0, axis=0)
    full_transfer_receipt: dict[str, float | int] = {}
    if selection == "transfer":
        selected, full_transfer_receipt = transfer_ranked_modes(
            field, wave, norm, dealias, target_shell, max_pairs, transfer_seed_count, rank_counts
        )
    else:
        selected = select_modes(field, norm, dealias, signed, target_shell, max_pairs, target_pairs)
    mode_index = {mode: index for index, mode in enumerate(selected)}
    packet = packet_mask(norm, target_shell)
    amplitudes_sq = np.asarray([
        float(np.sum(np.abs(coefficient_at(field, mode)) ** 2)) for mode in selected
    ])
    mass = float(np.sum(amplitudes_sq))
    if mass <= 1.0e-30:
        raise ValueError(f"{state_path}: selected carrier has zero modal mass")
    probability = amplitudes_sq / mass
    triads: list[dict[str, Any]] = []
    selected_rate = 0.0
    repeated_rate = 0.0
    for left, p_mode in enumerate(selected):
        u_p = coefficient_at(field, p_mode)
        p_vec = np.asarray(p_mode, dtype=np.float64)
        for right, q_mode in enumerate(selected):
            k_mode = (p_mode[0] + q_mode[0], p_mode[1] + q_mode[1], p_mode[2] + q_mode[2])
            out = mode_index.get(k_mode)
            if out is None:
                continue
            k_index = index_of(k_mode, n)
            if not bool(packet[k_index]) or not bool(dealias[k_index]):
                continue
            q_vec = np.asarray(q_mode, dtype=np.float64)
            u_q = coefficient_at(field, q_mode)
            u_k = coefficient_at(field, k_mode)
            contribution = leray(-1j * np.dot(q_vec, u_p) * u_q, np.asarray(k_mode, dtype=np.float64))
            transfer = float(2.0 * (2 ** target_shell) * np.real(np.vdot(u_k, contribution)))
            if left == right:
                repeated_rate += transfer
                continue
            amplitude_product = math.sqrt(float(probability[left] * probability[right] * probability[out]))
            if amplitude_product <= 1.0e-30:
                continue
            triads.append({"left": left, "right": right, "out": out,
                           "coefficient": transfer / amplitude_product})
            selected_rate += transfer

    # The probability carrier has unit total modal mass.  Multiplying the
    # viscosity by the observed mass makes its denominator equal the physical
    # 2 nu sum |k|^2 |u_k|^2 on this finite selected carrier.
    modes_json = [
        {"wavevector": list(mode), "dissipation_weight": float(np.dot(mode, mode))}
        for mode in selected
    ]
    selected_packet_dissipation = float(sum(
        float(modes_json[index]["dissipation_weight"]) * amplitudes_sq[index]
        for index, mode in enumerate(selected)
        if bool(packet[index_of(mode, n)])
    ))
    full_energy = np.sum(np.abs(field) ** 2, axis=0)
    full_dissipation = float(np.sum((norm ** 2) * full_energy * packet))
    # Full packet transfer is intentionally reconstructed elsewhere by the
    # existing pseudospectral path; this exporter only asserts its own finite
    # carrier accounting.
    packet_modal_energy = float(np.sum(full_energy[packet]))
    selected_packet_energy = float(sum(amplitudes_sq[index] for index, mode in enumerate(selected)
                                       if bool(packet[index_of(mode, n)])))
    metadata = {
        "source_state": str(state_path),
        "physical_viscosity": nu,
        "normalization_modal_mass": mass,
        "effective_profile_viscosity": nu * mass,
        "target_shell": target_shell,
        "selected_mode_count": len(selected),
        "selected_ordered_triad_count": len(triads),
        "selection_method": selection,
        "selected_signed_packet_rate": selected_rate,
        "omitted_repeated_input_signed_packet_rate": repeated_rate,
        "selected_packet_energy_fraction": (selected_packet_energy / packet_modal_energy
                                             if packet_modal_energy > 1.0e-30 else None),
        "selected_packet_dissipation_fraction": (selected_packet_dissipation / full_dissipation
                                                   if full_dissipation > 1.0e-30 else None),
        "carrier_scope": "finite selected modes; phases and polarizations frozen from raw_hat",
        "truth_authority": False,
        "theorem_authority": False,
        "promoted": False,
    }
    if full_transfer_receipt:
        selected_gross = sum(abs(float(triad["coefficient"]) * math.sqrt(
            float(probability[triad["left"]] * probability[triad["right"]] * probability[triad["out"]])
        )) for triad in triads)
        full_gross = float(full_transfer_receipt["full_packet_gross_activity"])
        full_rate = float(full_transfer_receipt["full_packet_signed_rate"])
        metadata.update(full_transfer_receipt)
        metadata.update({
            "selected_packet_signed_rate_fraction": (selected_rate / full_rate
                                                     if abs(full_rate) > 1.0e-30 else None),
            "selected_packet_gross_activity_fraction": (selected_gross / full_gross
                                                         if full_gross > 1.0e-30 else None),
        })
    problem = {
        "problem_id": state_path.stem,
        "viscosity": nu * mass,
        "convention": "left_plus_right_equals_out",
        "coefficient_semantics": "physical_leray_projected_frozen_phase_transfer_coefficient",
        "modes": modes_json,
        "triads": triads,
        "profiles": [{
            "profile_id": state_path.stem,
            "trajectory_id": trajectory_id,
            "time": time,
            "duration": duration,
            "cutoff": n,
            "probability": [float(value) for value in probability],
        }],
        "physical_export_receipt": metadata,
    }
    return problem, metadata


def main() -> None:
    args = parse_args()
    if args.target_shell < 0 or args.max_mode_pairs < 2 or args.target_mode_pairs < 1:
        raise ValueError("invalid shell or mode-pair limits")
    rank_counts = tuple(sorted({int(token) for token in args.transfer_rank_counts.split(",") if token.strip()}))
    if not rank_counts or rank_counts[0] < 1:
        raise ValueError("--transfer-rank-counts must contain positive integers")
    problems: list[dict[str, Any]] = []
    receipts: list[dict[str, Any]] = []
    time = 0.0
    for state in args.state:
        with np.load(state, allow_pickle=False) as data:
            nu = float(data["nu"]) if "nu" in data else 1.0e-3
            c = float(data["segment_window_c"]) if "segment_window_c" in data else 0.05
        duration_c = float(args.duration_c) if args.duration_c is not None else c
        duration = duration_c * (2.0 ** (-2 * args.target_shell)) / nu
        problem, receipt = export_problem(state, time, duration, args.target_shell,
                                          args.max_mode_pairs, args.target_mode_pairs,
                                          args.selection, args.transfer_seed_count, rank_counts,
                                          args.trajectory_id)
        problems.append(problem)
        receipts.append(receipt)
        time += duration
    payload = {
        "schema_version": "1.0.0",
        "script": SCRIPT_NAME,
        "authority": {"candidate_only": True, "empirical_non_promoting": True,
                      "truth_authority": False, "theorem_authority": False,
                      "clay_authority": False, "promoted": False},
        "coefficient_semantics": "physical Leray-projected frozen-phase finite carrier",
        "problems": problems,
        "export_receipts": receipts,
        "limitations": [
            "finite selected-mode carrier; omitted modes are not bounded",
            "p=q repeated-input triads are omitted because PR #15 currently requires distinct triad indices",
            "profile search varies modal magnitudes with observed phases and polarizations frozen",
        ],
    }
    atomic_json(args.output_json, payload)
    print(json.dumps({"output_json": str(args.output_json), "problem_count": len(problems),
                      "selected_triads": sum(len(problem["triads"]) for problem in problems)}, sort_keys=True))


if __name__ == "__main__":
    main()
