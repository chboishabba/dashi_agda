#!/usr/bin/env python3
"""Export exact transfer-rank capture curves from saved ``raw_hat`` states.

This is a finite, empirical, non-promoting diagnostic.  It enumerates the same
Leray-projected ordered Fourier interactions used by
``ns_triad_gamma_gap_raw_hat_export.py`` but keeps the largest transfer atoms in
an efficient bounded structured array.  The resulting receipt answers two
questions which the selected-carrier Gamma audit cannot answer:

* how many ordered transfer atoms are required to capture a requested fraction
  of gross packet activity; and
* how many reality-closed Fourier modes are induced by those leading atoms.

No sampled capture curve is a cutoff-uniform estimate or a Navier--Stokes
regularity theorem.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any, Iterable

import numpy as np

from ns_triad_gamma_gap_raw_hat_export import atomic_json, frequency_data, packet_mask


SCRIPT_NAME = "scripts/ns_triad_transfer_rank_capture_curve.py"

RECORD_DTYPE = np.dtype(
    [
        ("value", np.float64),
        ("kx", np.int16), ("ky", np.int16), ("kz", np.int16),
        ("px", np.int16), ("py", np.int16), ("pz", np.int16),
        ("qx", np.int16), ("qy", np.int16), ("qz", np.int16),
    ]
)


def parse_int_list(raw: str) -> tuple[int, ...]:
    values = tuple(sorted({int(token.strip()) for token in raw.split(",") if token.strip()}))
    if not values or values[0] < 1:
        raise ValueError("rank list must contain positive integers")
    return values


def parse_fraction_list(raw: str) -> tuple[float, ...]:
    values = tuple(sorted({float(token.strip()) for token in raw.split(",") if token.strip()}))
    if not values or any(not math.isfinite(value) or value <= 0.0 or value > 1.0 for value in values):
        raise ValueError("capture targets must lie in (0, 1]")
    return values


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--state", type=Path, action="append", required=True,
                        help="saved NPZ containing raw_hat; may be repeated")
    parser.add_argument("--target-shell", type=int, default=2)
    parser.add_argument(
        "--rank-counts",
        default="1,8,64,512,4096,32768,262144",
        help="comma-separated exact top-atom ranks to report",
    )
    parser.add_argument(
        "--capture-targets",
        default="0.5,0.9",
        help="comma-separated gross-activity fractions whose first attaining rank is requested",
    )
    parser.add_argument("--output-json", type=Path, required=True)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def representative(mode: tuple[int, int, int]) -> tuple[int, int, int]:
    negated = (-mode[0], -mode[1], -mode[2])
    return min(mode, negated)


def _records_for_chunk(
    absolute_transfer: np.ndarray,
    k_mode: np.ndarray,
    p_modes: np.ndarray,
    q_modes: np.ndarray,
) -> np.ndarray:
    values = np.asarray(absolute_transfer, dtype=np.float64)
    finite = np.isfinite(values) & (values > 0.0)
    if not np.any(finite):
        return np.empty(0, dtype=RECORD_DTYPE)
    values = values[finite]
    p = np.asarray(p_modes[finite], dtype=np.int16)
    q = np.asarray(q_modes[finite], dtype=np.int16)
    k = np.asarray(k_mode, dtype=np.int16)
    records = np.empty(len(values), dtype=RECORD_DTYPE)
    records["value"] = values
    records["kx"], records["ky"], records["kz"] = int(k[0]), int(k[1]), int(k[2])
    records["px"], records["py"], records["pz"] = p[:, 0], p[:, 1], p[:, 2]
    records["qx"], records["qy"], records["qz"] = q[:, 0], q[:, 1], q[:, 2]
    return records


def retain_top_records(current: np.ndarray, incoming: np.ndarray, limit: int) -> np.ndarray:
    """Retain the exact largest ``limit`` records by ``value``.

    The function is order-independent and uses ``argpartition`` rather than a
    Python object heap, keeping the N32 scan memory bounded even for hundreds of
    thousands of retained atoms.
    """
    if limit < 1:
        raise ValueError("limit must be positive")
    if len(incoming) == 0:
        return np.asarray(current, dtype=RECORD_DTYPE)
    if len(current) == 0:
        merged = np.asarray(incoming, dtype=RECORD_DTYPE)
    else:
        merged = np.concatenate((np.asarray(current, dtype=RECORD_DTYPE),
                                 np.asarray(incoming, dtype=RECORD_DTYPE)))
    if len(merged) <= limit:
        return merged
    indices = np.argpartition(merged["value"], len(merged) - limit)[-limit:]
    return merged[indices]


def _record_modes(record: np.void) -> Iterable[tuple[int, int, int]]:
    yield int(record["kx"]), int(record["ky"]), int(record["kz"])
    yield int(record["px"]), int(record["py"]), int(record["pz"])
    yield int(record["qx"]), int(record["qy"]), int(record["qz"])


def capture_summary(
    retained: np.ndarray,
    *,
    full_gross: float,
    total_atom_count: int,
    rank_counts: tuple[int, ...],
    capture_targets: tuple[float, ...],
) -> dict[str, Any]:
    """Return exact rank points and target ranks within the retained prefix."""
    if full_gross < 0.0 or not math.isfinite(full_gross):
        raise ValueError("full_gross must be finite and nonnegative")
    ordered = np.sort(np.asarray(retained, dtype=RECORD_DTYPE), order="value")[::-1]
    cumulative = np.cumsum(ordered["value"], dtype=np.float64)
    requested = set(rank_counts)
    representatives: set[tuple[int, int, int]] = set()
    points: list[dict[str, Any]] = []
    mode_count_at_rank: dict[int, int] = {}

    target_indices: dict[float, int | None] = {}
    for target in capture_targets:
        if full_gross <= 0.0 or len(cumulative) == 0:
            target_indices[target] = None
            continue
        index = int(np.searchsorted(cumulative, target * full_gross, side="left"))
        target_indices[target] = index if index < len(cumulative) else None

    interesting_ranks = requested | {
        index + 1 for index in target_indices.values() if index is not None
    }
    for index, record in enumerate(ordered, start=1):
        for mode in _record_modes(record):
            if mode != (0, 0, 0):
                representatives.add(representative(mode))
        if index in interesting_ranks:
            mode_count_at_rank[index] = 2 * len(representatives)
        if index in requested:
            gross = float(cumulative[index - 1])
            points.append(
                {
                    "rank": index,
                    "gross_activity": gross,
                    "gross_activity_fraction": gross / full_gross if full_gross > 0.0 else 0.0,
                    "reality_closed_mode_count": 2 * len(representatives),
                    "reality_pair_count": len(representatives),
                }
            )

    retained_count = len(ordered)
    retained_gross = float(cumulative[-1]) if retained_count else 0.0
    for rank in rank_counts:
        if rank <= retained_count:
            continue
        # This only occurs when the whole finite carrier has fewer atoms than a
        # requested rank, because retained_count is bounded by max(rank_counts).
        points.append(
            {
                "rank": rank,
                "available_atom_count": total_atom_count,
                "gross_activity": retained_gross,
                "gross_activity_fraction": retained_gross / full_gross if full_gross > 0.0 else 0.0,
                "reality_closed_mode_count": 2 * len(representatives),
                "reality_pair_count": len(representatives),
                "rank_exceeds_atom_count": True,
            }
        )

    targets: list[dict[str, Any]] = []
    for target in capture_targets:
        index = target_indices[target]
        if index is not None:
            rank = index + 1
            targets.append(
                {
                    "target_fraction": target,
                    "reached_within_retained_prefix": True,
                    "exact_atom_rank": rank,
                    "gross_activity_fraction_at_rank": float(cumulative[index] / full_gross),
                    "reality_closed_mode_count_at_rank": mode_count_at_rank[rank],
                }
            )
        else:
            targets.append(
                {
                    "target_fraction": target,
                    "reached_within_retained_prefix": False,
                    "atom_rank_lower_bound": retained_count + 1,
                    "gross_activity_fraction_at_retained_limit": (
                        retained_gross / full_gross if full_gross > 0.0 else 0.0
                    ),
                    "reality_closed_mode_count_lower_bound": 2 * len(representatives),
                }
            )

    return {
        "retained_top_atom_limit": retained_count,
        "total_atom_count": int(total_atom_count),
        "rank_curve": sorted(points, key=lambda point: int(point["rank"])),
        "capture_target_rank_bounds": targets,
    }


def scan_state(
    state_path: Path,
    *,
    target_shell: int,
    rank_counts: tuple[int, ...],
    capture_targets: tuple[float, ...],
) -> dict[str, Any]:
    with np.load(state_path, allow_pickle=False) as data:
        raw = np.asarray(data["raw_hat"], dtype=np.complex128)
        viscosity = float(data["nu"]) if "nu" in data else 1.0e-3
    if raw.ndim != 4 or raw.shape[-1] != 3 or len(set(raw.shape[:3])) != 1:
        raise ValueError(f"{state_path}: expected raw_hat shape (N,N,N,3), got {raw.shape!r}")
    if target_shell < 0:
        raise ValueError("target_shell must be nonnegative")

    n = int(raw.shape[0])
    field = np.moveaxis(raw / float(n ** 3), -1, 0)
    wave, norm, _norm_sq, _signed = frequency_data(n)
    dealias = np.all(np.abs(wave) <= float(n) / 3.0, axis=0)
    packet = packet_mask(norm, target_shell) & dealias
    nonzero = dealias & (norm > 0.0)
    all_indices = np.argwhere(nonzero)
    p_modes = np.stack((wave[0][nonzero], wave[1][nonzero], wave[2][nonzero]), axis=1).astype(np.int64)
    p_coeff = field[:, all_indices[:, 0], all_indices[:, 1], all_indices[:, 2]].T
    cutoff = n // 3
    retain_limit = max(rank_counts)

    top_all = np.empty(0, dtype=RECORD_DTYPE)
    top_distinct = np.empty(0, dtype=RECORD_DTYPE)
    full_signed = 0.0
    full_gross = 0.0
    distinct_signed = 0.0
    distinct_gross = 0.0
    repeated_signed = 0.0
    repeated_gross = 0.0
    all_count = 0
    distinct_count = 0
    repeated_count = 0

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
        transfer = 2.0 * (2 ** target_shell) * np.real(
            np.einsum("j,ij->i", np.conjugate(field[:, z, y, x]), forcing)
        )
        absolute = np.abs(transfer)
        repeated = np.all(p == q, axis=1)
        distinct = ~repeated

        full_signed += float(np.sum(transfer))
        full_gross += float(np.sum(absolute))
        repeated_signed += float(np.sum(transfer[repeated]))
        repeated_gross += float(np.sum(absolute[repeated]))
        distinct_signed += float(np.sum(transfer[distinct]))
        distinct_gross += float(np.sum(absolute[distinct]))
        all_count += int(len(transfer))
        repeated_count += int(np.count_nonzero(repeated))
        distinct_count += int(np.count_nonzero(distinct))

        top_all = retain_top_records(
            top_all,
            _records_for_chunk(absolute, k_mode, p, q),
            retain_limit,
        )
        top_distinct = retain_top_records(
            top_distinct,
            _records_for_chunk(absolute[distinct], k_mode, p[distinct], q[distinct]),
            retain_limit,
        )

    return {
        "source_state": str(state_path),
        "grid_size": n,
        "physical_viscosity": viscosity,
        "target_shell": target_shell,
        "full_packet_signed_rate": full_signed,
        "full_packet_gross_activity": full_gross,
        "distinct_input_signed_rate": distinct_signed,
        "distinct_input_gross_activity": distinct_gross,
        "repeated_input_signed_rate": repeated_signed,
        "repeated_input_gross_activity": repeated_gross,
        "all_ordered_atom_count": all_count,
        "distinct_input_atom_count": distinct_count,
        "repeated_input_atom_count": repeated_count,
        "all_atoms": capture_summary(
            top_all,
            full_gross=full_gross,
            total_atom_count=all_count,
            rank_counts=rank_counts,
            capture_targets=capture_targets,
        ),
        "distinct_input_atoms": capture_summary(
            top_distinct,
            full_gross=distinct_gross,
            total_atom_count=distinct_count,
            rank_counts=rank_counts,
            capture_targets=capture_targets,
        ),
        "truth_authority": False,
        "theorem_authority": False,
        "clay_authority": False,
        "promoted": False,
    }


def main() -> None:
    args = parse_args()
    rank_counts = parse_int_list(args.rank_counts)
    capture_targets = parse_fraction_list(args.capture_targets)
    receipts = [
        scan_state(
            path,
            target_shell=args.target_shell,
            rank_counts=rank_counts,
            capture_targets=capture_targets,
        )
        for path in args.state
    ]
    payload = {
        "schema_version": "1.0.0",
        "script": SCRIPT_NAME,
        "authority": {
            "candidate_only": True,
            "empirical_non_promoting": True,
            "truth_authority": False,
            "theorem_authority": False,
            "clay_authority": False,
            "promoted": False,
        },
        "rank_counts": list(rank_counts),
        "capture_targets": list(capture_targets),
        "receipts": receipts,
        "limitations": [
            "finite Galerkin checkpoints only",
            "capture rank is not a cutoff-uniform compactness estimate",
            "reality-closed mode counts are induced by leading observed atoms and do not prove carrier closure",
        ],
    }
    atomic_json(args.output_json, payload)
    if args.pretty:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(json.dumps({"output_json": str(args.output_json), "receipt_count": len(receipts)}, sort_keys=True))


if __name__ == "__main__":
    main()
