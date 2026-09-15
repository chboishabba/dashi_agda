from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Iterable

CHUNKS: dict[str, tuple[int, ...]] = {
    "worlds00to07": tuple(range(0, 8)),
    "worlds08to15": tuple(range(8, 16)),
    "worlds16to23": tuple(range(16, 24)),
    "worlds24to33": tuple(range(24, 34)),
}

UNIVERSAL_RANK_COORDINATE_COUNT = 14


def _require_int(value: Any, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise ValueError(f"{name} must be an integer")
    return value


def _validate_row(row: dict[str, Any]) -> None:
    _require_int(row.get("world_id"), "world_id")
    action_digest = row.get("action_digest")
    if not isinstance(action_digest, str) or not action_digest:
        raise ValueError("action_digest must be a non-empty string")
    _require_int(row.get("rank_r2"), "rank_r2")
    _require_int(row.get("rank_r10"), "rank_r10")
    all_ranks = row.get("all_ranks")
    if not isinstance(all_ranks, list) or len(all_ranks) != UNIVERSAL_RANK_COORDINATE_COUNT:
        raise ValueError(
            f"all_ranks must contain exactly {UNIVERSAL_RANK_COORDINATE_COUNT} rank coordinates"
        )
    for index, rank in enumerate(all_ranks):
        _require_int(rank, f"all_ranks[{index}]")


def build_verified_chunk_receipt(
    chunk: str,
    rows: Iterable[dict[str, Any]],
) -> dict[str, Any]:
    if chunk not in CHUNKS:
        raise ValueError(f"unknown chunk {chunk!r}")

    materialized = list(rows)
    expected_ids = CHUNKS[chunk]
    expected_count = len(expected_ids)
    if len(materialized) != expected_count:
        raise ValueError(
            f"chunk {chunk} expected {expected_count} worlds, got {len(materialized)}"
        )

    for row in materialized:
        if not isinstance(row, dict):
            raise ValueError("each world row must be a JSON object")
        _validate_row(row)

    observed_ids = tuple(sorted(_require_int(row["world_id"], "world_id") for row in materialized))
    if observed_ids != expected_ids:
        raise ValueError(
            f"chunk {chunk} world ids must be {list(expected_ids)}, got {list(observed_ids)}"
        )

    ordered_rows = sorted(materialized, key=lambda row: int(row["world_id"]))
    return {
        "schema": "rsa260-bidi-mksol-action-chunk-receipt-v1",
        "chunk": chunk,
        "expected_world_ids": list(expected_ids),
        "expected_world_count": expected_count,
        "completed_world_count": len(ordered_rows),
        "complete": True,
        "action_outputs_retained": True,
        "rank_r2_retained": True,
        "rank_r10_retained": True,
        "all_universally_available_rank_coordinates_retained": True,
        "worlds": ordered_rows,
    }


def _load_rows(path: Path) -> list[dict[str, Any]]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if isinstance(payload, dict) and isinstance(payload.get("worlds"), list):
        payload = payload["worlds"]
    if not isinstance(payload, list):
        raise ValueError("input JSON must be a list of world rows or an object with a worlds list")
    if not all(isinstance(row, dict) for row in payload):
        raise ValueError("each world row must be a JSON object")
    return payload


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Validate one bounded RSA260 synthetic mksol-action chunk receipt."
    )
    parser.add_argument("--chunk", required=True, choices=tuple(CHUNKS))
    parser.add_argument("--input", required=True, type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    receipt = build_verified_chunk_receipt(args.chunk, _load_rows(args.input))
    rendered = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.output is None:
        print(rendered, end="")
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
