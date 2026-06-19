#!/usr/bin/env python3
"""Build Calc12 pair JSON from derived NS ``.npz`` archives.

The builder combines one or more derived archives into a single Calc12 dataset
entry with a deterministic pair ordering.  It is fail-closed: every archive
must provide ``g12`` and one accepted omega/e2 source field, and any requested
``lambda2`` band filter is only applied when ``lambda2`` is present.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

import numpy as np


CONTRACT = "ns_clay_calc12_pair_builder"
VERSION = 1
DEFAULT_OUTPUT = Path("outputs") / f"{CONTRACT}.json"

AUTHORITY_FLAGS = {
    "candidate_only": True,
    "clay_authority": False,
    "empirical_non_promoting": True,
    "promoted": False,
    "runtime_authority": False,
    "theorem_authority": False,
    "truth_authority": False,
}

OMEGA_DIRECT_KEYS = (
    "omega_e2_projection_sq",
    "omega_dot_e2_sq",
    "omega_e2_sq",
)
OMEGA_FALLBACK_KEYS = ("omega_e2_fraction", "omega_sq")


class InputError(ValueError):
    """Raised when the input archives do not satisfy the builder contract."""


@dataclass(frozen=True)
class CollectedPair:
    source: str
    flat_index: int
    g12: float
    omega_e2_sq: float

    def as_pair(self) -> dict[str, float]:
        return {"g12": self.g12, "omega_e2_sq": self.omega_e2_sq}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--input",
        action="append",
        required=True,
        type=Path,
        help="Path to a derived .npz archive or a directory containing .npz archives. May be repeated.",
    )
    parser.add_argument("--output", required=True, type=Path, help="Path to write the Calc12 JSON payload.")
    parser.add_argument(
        "--datum-id",
        help="Datum identifier for the emitted Calc12 dataset. Defaults to the source stem or a pooled id.",
    )
    parser.add_argument(
        "--lambda2-band",
        type=float,
        help="Optional band filter; keep entries with abs(lambda2) <= band when lambda2 exists.",
    )
    parser.add_argument(
        "--max-pairs",
        type=int,
        help="Optional deterministic cap after sorting by (source, flat_index).",
    )
    return parser.parse_args()


def read_npz(path: Path) -> dict[str, np.ndarray]:
    try:
        with np.load(path, allow_pickle=False) as data:
            return {name: np.asarray(data[name]) for name in data.files}
    except FileNotFoundError as exc:
        raise InputError(f"input archive does not exist: {path}") from exc
    except Exception as exc:
        raise InputError(f"failed to read .npz archive {path}: {exc}") from exc


def _as_real_array(name: str, value: Any, *, source: Path) -> np.ndarray:
    array = np.asarray(value)
    if np.iscomplexobj(array):
        imag = np.asarray(array.imag, dtype=np.float64)
        if np.any(imag != 0.0):
            raise InputError(f"{source}: field {name!r} must be real-valued")
        array = np.asarray(array.real)
    array = np.asarray(array, dtype=np.float64)
    if array.size == 0:
        raise InputError(f"{source}: field {name!r} must not be empty")
    if not np.all(np.isfinite(array)):
        raise InputError(f"{source}: field {name!r} contains non-finite values")
    return array


def _shape_mismatch(source: Path, *items: tuple[str, tuple[int, ...]]) -> InputError:
    details = ", ".join(f"{name}={shape!r}" for name, shape in items)
    return InputError(f"{source}: field shapes must match, got {details}")


def _expand_input_path(path: Path) -> list[Path]:
    if not path.exists():
        raise InputError(f"input path does not exist: {path}")
    if path.is_dir():
        files = sorted(
            candidate for candidate in path.iterdir() if candidate.is_file() and candidate.suffix.lower() == ".npz"
        )
        if not files:
            raise InputError(f"input directory contains no .npz archives: {path}")
        return files
    if path.is_file():
        if path.suffix.lower() != ".npz":
            raise InputError(f"input file must have a .npz suffix: {path}")
        return [path]
    raise InputError(f"unsupported input path type: {path}")


def collect_input_paths(inputs: Iterable[Path]) -> list[Path]:
    seen: set[str] = set()
    ordered: list[Path] = []
    for raw_path in inputs:
        for path in _expand_input_path(raw_path):
            resolved = str(path.resolve())
            if resolved in seen:
                continue
            seen.add(resolved)
            ordered.append(path)
    if not ordered:
        raise InputError("no .npz archives were collected from the provided --input paths")
    return sorted(ordered, key=lambda candidate: str(candidate.resolve()))


def resolve_omega_field(data: dict[str, np.ndarray], *, source: Path) -> tuple[np.ndarray, str, str]:
    for key in OMEGA_DIRECT_KEYS:
        if key in data:
            return _as_real_array(key, data[key], source=source), key, key

    if all(key in data for key in OMEGA_FALLBACK_KEYS):
        fraction = _as_real_array("omega_e2_fraction", data["omega_e2_fraction"], source=source)
        omega_sq = _as_real_array("omega_sq", data["omega_sq"], source=source)
        if fraction.shape != omega_sq.shape:
            raise _shape_mismatch(source, ("omega_e2_fraction", fraction.shape), ("omega_sq", omega_sq.shape))
        return fraction * omega_sq, "omega_e2_fraction*omega_sq", "omega_e2_fraction,omega_sq"

    missing = [key for key in (*OMEGA_DIRECT_KEYS, *OMEGA_FALLBACK_KEYS) if key not in data]
    raise InputError(
        f"{source}: missing accepted omega/e2 keys; need one of {list(OMEGA_DIRECT_KEYS)!r} or both "
        f"{list(OMEGA_FALLBACK_KEYS)!r}; missing={missing!r}"
    )


def load_pairs_from_archive(path: Path, *, lambda2_band: float | None) -> tuple[list[CollectedPair], dict[str, Any]]:
    data = read_npz(path)
    if "g12" not in data:
        raise InputError(f"{path}: missing required key 'g12'")

    g12 = _as_real_array("g12", data["g12"], source=path)
    omega_e2_sq, omega_key, omega_source = resolve_omega_field(data, source=path)
    if g12.shape != omega_e2_sq.shape:
        raise _shape_mismatch(path, ("g12", g12.shape), ("omega_e2_sq", omega_e2_sq.shape))

    lambda2_used = False
    lambda2_shape: tuple[int, ...] | None = None
    if lambda2_band is not None and "lambda2" in data:
        lambda2 = _as_real_array("lambda2", data["lambda2"], source=path)
        lambda2_shape = lambda2.shape
        if lambda2.shape != g12.shape:
            raise _shape_mismatch(path, ("g12", g12.shape), ("lambda2", lambda2.shape), ("omega_e2_sq", omega_e2_sq.shape))
        mask = np.abs(lambda2) <= lambda2_band
        lambda2_used = True
    else:
        mask = np.ones(g12.shape, dtype=bool)

    flat_g12 = np.ravel(g12)
    flat_omega = np.ravel(omega_e2_sq)
    flat_mask = np.ravel(mask)
    source_name = str(path.resolve())
    pairs: list[CollectedPair] = []
    for flat_index, keep in enumerate(flat_mask):
        if not bool(keep):
            continue
        g12_value = float(flat_g12[flat_index])
        omega_value = float(flat_omega[flat_index])
        if not (math.isfinite(g12_value) and math.isfinite(omega_value)):
            raise InputError(f"{path}: non-finite pair encountered at flat_index={flat_index}")
        pairs.append(
            CollectedPair(
                source=source_name,
                flat_index=flat_index,
                g12=g12_value,
                omega_e2_sq=omega_value,
            )
        )

    metadata = {
        "source_path": str(path),
        "resolved_source_path": source_name,
        "pair_count_raw": int(flat_g12.size),
        "pair_count_after_lambda2": len(pairs),
        "lambda2_band": lambda2_band,
        "lambda2_present": "lambda2" in data,
        "lambda2_band_applied": lambda2_used,
        "lambda2_shape": list(lambda2_shape) if lambda2_shape is not None else None,
        "g12_shape": list(g12.shape),
        "omega_field_key": omega_key,
        "omega_field_source": omega_source,
    }
    return pairs, metadata


def _choose_datum_id(paths: list[Path], requested: str | None) -> str:
    if requested:
        return requested
    if len(paths) == 1:
        return paths[0].stem
    return "calc12_pair_pool"


def build_payload(args: argparse.Namespace) -> dict[str, Any]:
    if args.lambda2_band is not None and args.lambda2_band < 0.0:
        raise InputError("--lambda2-band must be non-negative")
    if args.max_pairs is not None and args.max_pairs <= 0:
        raise InputError("--max-pairs must be positive")

    source_paths = collect_input_paths(args.input)
    collected: list[CollectedPair] = []
    per_source_metadata: list[dict[str, Any]] = []
    for path in source_paths:
        source_pairs, metadata = load_pairs_from_archive(path, lambda2_band=args.lambda2_band)
        collected.extend(source_pairs)
        per_source_metadata.append(metadata)

    if not collected:
        raise InputError("no usable pairs were found after loading all archives")

    collected.sort(key=lambda item: (item.source, item.flat_index))
    total_pairs = len(collected)
    if args.max_pairs is not None and total_pairs > args.max_pairs:
        collected = collected[: args.max_pairs]

    datum_id = _choose_datum_id(source_paths, args.datum_id)
    pairs = [pair.as_pair() for pair in collected]

    dataset_metadata = {
        "authority": dict(AUTHORITY_FLAGS),
        "source_count": len(source_paths),
        "source_paths": [str(path) for path in source_paths],
        "source_metadata": per_source_metadata,
        "pair_count_raw": total_pairs,
        "pair_count_used": len(pairs),
        "sort_order": ["source", "flat_index"],
        "downsampled": args.max_pairs is not None and total_pairs > args.max_pairs,
        "max_pairs": args.max_pairs,
        "lambda2_band": args.lambda2_band,
    }

    payload = {
        "contract": CONTRACT,
        "version": VERSION,
        "authority": dict(AUTHORITY_FLAGS),
        "metadata": {
            "authority": dict(AUTHORITY_FLAGS),
            "input_paths": [str(path) for path in args.input],
            "source_paths": [str(path) for path in source_paths],
            "lambda2_band": args.lambda2_band,
            "max_pairs": args.max_pairs,
            "sort_order": ["source", "flat_index"],
            "downsample_rule": "prefix_after_sort" if args.max_pairs is not None else None,
        },
        "datasets": [
            {
                "datum_id": datum_id,
                "pairs": pairs,
                "metadata": dataset_metadata,
            }
        ],
    }
    return payload


def validate_payload(payload: dict[str, Any]) -> None:
    if not isinstance(payload, dict):
        raise InputError("internal validation failed: payload must be an object")
    required_top_level = {"contract", "version", "authority", "metadata", "datasets"}
    if required_top_level - set(payload):
        raise InputError(
            f"internal validation failed: missing top-level keys {sorted(required_top_level - set(payload))!r}"
        )
    if payload["contract"] != CONTRACT:
        raise InputError("internal validation failed: contract mismatch")
    if payload["version"] != VERSION:
        raise InputError("internal validation failed: version mismatch")
    if payload["authority"] != AUTHORITY_FLAGS:
        raise InputError("internal validation failed: top-level authority flags mismatch")
    datasets = payload["datasets"]
    if not isinstance(datasets, list) or len(datasets) != 1:
        raise InputError("internal validation failed: datasets must be a single-item list")
    dataset = datasets[0]
    if not isinstance(dataset, dict):
        raise InputError("internal validation failed: dataset must be an object")
    if {"datum_id", "pairs", "metadata"} - set(dataset):
        raise InputError("internal validation failed: dataset missing required keys")
    if not isinstance(dataset["pairs"], list) or not dataset["pairs"]:
        raise InputError("internal validation failed: dataset pairs must be a non-empty list")
    for pair_index, pair in enumerate(dataset["pairs"]):
        if not isinstance(pair, dict):
            raise InputError(f"internal validation failed: pair {pair_index} must be an object")
        if set(pair) != {"g12", "omega_e2_sq"}:
            raise InputError(f"internal validation failed: pair {pair_index} must contain only g12 and omega_e2_sq")
    metadata = dataset["metadata"]
    if not isinstance(metadata, dict):
        raise InputError("internal validation failed: dataset metadata must be an object")
    if metadata.get("authority") != AUTHORITY_FLAGS:
        raise InputError("internal validation failed: dataset authority flags mismatch")


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(value, separators=(",", ":"), sort_keys=True, ensure_ascii=False) + "\n"
    path.write_text(text, encoding="utf-8")
    print(text, end="")


def main() -> int:
    args = parse_args()
    try:
        payload = build_payload(args)
        validate_payload(payload)
        write_json(args.output, payload)
    except InputError as exc:
        print(str(exc), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
