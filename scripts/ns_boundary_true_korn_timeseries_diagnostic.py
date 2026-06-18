#!/usr/bin/env python3
"""Calc 9 true-Korn timeseries diagnostic for NS boundary carriers.

The runner consumes either:

* a raw velocity/pressure ``.npz`` archive with one or more snapshots, or
* a directory of derived per-frame ``.npz`` archives.

Carrier components are selected from either:

* an existing carrier-timeseries JSON payload, or
* explicit ``frame:component`` pairs on the CLI.

For each selected frame, the runner reuses the existing
``ns_boundary_korn_ratio_diagnostic`` logic on a per-frame derived archive and
requires the true denominator field to be canonicalized as
``velocity_hessian_norm_squared``.  The output is a fail-closed JSON payload
with per-frame rows and a summary.
"""

from __future__ import annotations

import argparse
import json
import math
import re
import sys
import tempfile
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

import scripts.ns_boundary_derived_tensor_archive as derived_archive
import scripts.ns_boundary_korn_ratio_diagnostic as korn_diag
from scripts.ns_boundary_layer_thickness_diagnostic import _label_components


SCRIPT_NAME = "scripts/ns_boundary_true_korn_timeseries_diagnostic.py"
CONTRACT = "ns_boundary_true_korn_timeseries_diagnostic"
DEFAULT_LAMBDA2_BAND = 1.0e-3
TRUE_DENOMINATOR_FIELD = "velocity_hessian_norm_squared"
ALIAS_DENOMINATOR_FIELD = "u_hessian_norm_squared"
FRAME_NUMBER_RE = re.compile(r"(?:^|[_-])frame[_-]?(\d+)(?:\D|$)")


@dataclass(frozen=True)
class CarrierSelection:
    frame: int
    component_id: int


def _positive_int(value: str) -> int:
    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("value must be a positive integer")
    return parsed


def _finite_nonnegative_float(value: str) -> float:
    parsed = float(value)
    if not math.isfinite(parsed) or parsed < 0.0:
        raise argparse.ArgumentTypeError("value must be finite and nonnegative")
    return parsed


def _json_text(payload: dict[str, Any]) -> str:
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _load_npz(path: Path) -> dict[str, np.ndarray]:
    return derived_archive._load_npz(path)


def _frame_count_from_raw_archive(data: dict[str, np.ndarray]) -> int:
    u, _, _, _, _ = derived_archive._load_velocity_components(data, None)
    if u.ndim == 3:
        return 1
    if u.ndim == 4:
        return int(u.shape[0])
    raise ValueError(f"unsupported raw velocity rank: {u.shape!r}")


def _looks_like_derived_archive(data: dict[str, np.ndarray]) -> bool:
    return "lambda2" in data and "g12" in data and ("B_k" in data or "B_k_max" in data) and "pressure_hessian_norm" in data


def _frame_count_from_derived_archive(data: dict[str, np.ndarray]) -> int:
    counts: set[int] = set()
    saw_3d = False
    for name in ("lambda2", "g12", "B_k", "B_k_max", "pressure_hessian_norm", TRUE_DENOMINATOR_FIELD, ALIAS_DENOMINATOR_FIELD):
        if name not in data:
            continue
        value = np.asarray(data[name])
        if value.ndim == 4:
            counts.add(int(value.shape[0]))
        elif value.ndim == 3:
            saw_3d = True
        elif value.shape == () or value.ndim == 1:
            continue
        else:
            raise ValueError(f"{name} must be 3D/4D tensor or scalar/per-frame metadata, got {value.shape!r}")
    if counts and saw_3d:
        raise ValueError("mixed 3D and 4D tensor fields are not supported in one derived archive")
    if len(counts) > 1:
        raise ValueError(f"derived tensor frame counts do not match: {sorted(counts)!r}")
    if counts:
        return counts.pop()
    if saw_3d:
        return 1
    raise ValueError("derived archive is missing 3D/4D tensor fields")


def _slice_for_frame(array: np.ndarray, frame_index: int, frame_count: int) -> np.ndarray:
    value = np.asarray(array)
    if value.ndim >= 1 and int(value.shape[0]) == frame_count:
        return np.asarray(value[frame_index])
    return value


def _write_npz(path: Path, payload: dict[str, Any]) -> None:
    derived_archive._write_npz_atomic(path, payload)


def _parse_carrier_pair(value: str) -> CarrierSelection:
    if ":" not in value:
        raise argparse.ArgumentTypeError("carrier pairs must use frame:component syntax")
    frame_text, component_text = value.split(":", 1)
    try:
        frame = int(frame_text)
        component_id = int(component_text)
    except Exception as exc:  # pragma: no cover - argparse wraps this
        raise argparse.ArgumentTypeError("carrier pairs must contain integer frame and component ids") from exc
    if frame < 0:
        raise argparse.ArgumentTypeError("frame must be nonnegative")
    if component_id <= 0:
        raise argparse.ArgumentTypeError("component id must be positive")
    return CarrierSelection(frame=frame, component_id=component_id)


def _parse_component_map(text: str) -> dict[int, int]:
    out: dict[int, int] = {}
    if not text.strip():
        return out
    for chunk in text.split(","):
        chunk = chunk.strip()
        if not chunk:
            continue
        left, sep, right = chunk.partition(":")
        if sep != ":":
            raise ValueError(f"component-map entry must be frame:component, got {chunk!r}")
        frame = int(left)
        component_id = int(right)
        if frame < 0 or component_id <= 0:
            raise ValueError(
                f"component-map values must be nonnegative frame and positive component, got {chunk!r}"
            )
        if frame in out:
            raise ValueError(f"duplicate carrier selection for frame {frame}")
        out[frame] = component_id
    return out


def _carrier_map_from_json(path: Path) -> tuple[dict[int, int], dict[str, Any]]:
    with path.open("r", encoding="utf-8") as handle:
        payload = json.load(handle)
    if not isinstance(payload, dict):
        raise ValueError("carrier-timeseries JSON must contain an object at the top level")
    rows = payload.get("rows")
    if not isinstance(rows, list):
        raise ValueError("carrier-timeseries JSON must contain a top-level rows array")

    carrier_map: dict[int, int] = {}
    layer_thickness_by_frame: dict[str, float] = {}
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            raise ValueError(f"row {index} is not an object")
        status = str(row.get("status", "ok"))
        if status != "ok":
            raise ValueError(f"row {index} has non-ok status {status!r}")
        if "frame" not in row:
            raise ValueError(f"row {index} is missing frame")
        if "carrier_id" not in row and "primary_carrier_id" not in row:
            raise ValueError(f"row {index} is missing carrier_id")
        frame = int(row["frame"])
        carrier_id = int(row.get("carrier_id", row.get("primary_carrier_id")))
        if frame < 0:
            raise ValueError(f"row {index} has negative frame {frame}")
        if carrier_id <= 0:
            raise ValueError(f"row {index} has invalid carrier_id {carrier_id}")
        if frame in carrier_map:
            raise ValueError(f"duplicate frame {frame} in carrier-timeseries JSON")
        carrier_map[frame] = carrier_id
        layer_thickness = row.get("layer_thickness_physical_mean", row.get("layer_thickness_mean"))
        if layer_thickness is not None:
            layer_value = float(layer_thickness)
            if math.isfinite(layer_value) and layer_value >= 0.0:
                layer_thickness_by_frame[str(frame)] = layer_value

    return carrier_map, {
        "kind": "carrier_timeseries_json",
        "path": str(path),
        "row_count": len(rows),
        "layer_thickness_physical_by_frame": layer_thickness_by_frame,
    }


def _carrier_map_from_pairs(pairs: list[CarrierSelection]) -> tuple[dict[int, int], dict[str, Any]]:
    carrier_map: dict[int, int] = {}
    for pair in pairs:
        if pair.frame in carrier_map:
            raise ValueError(f"duplicate carrier selection for frame {pair.frame}")
        carrier_map[pair.frame] = pair.component_id
    return carrier_map, {"kind": "explicit_pairs", "path": None, "row_count": len(pairs)}


def _carrier_map_auto() -> tuple[dict[int, int], dict[str, Any]]:
    return {}, {"kind": "auto_largest_component", "path": None, "row_count": 0}


def _normalize_true_denominator_archive(source_path: Path, tmpdir: Path) -> Path:
    with np.load(source_path, allow_pickle=False) as data:
        has_true = TRUE_DENOMINATOR_FIELD in data
        has_alias = ALIAS_DENOMINATOR_FIELD in data
        if has_true and not has_alias:
            return source_path
        if not has_alias:
            raise ValueError(
                f"{source_path} does not contain {TRUE_DENOMINATOR_FIELD} or {ALIAS_DENOMINATOR_FIELD}"
            )

        alias_values = np.asarray(data[ALIAS_DENOMINATOR_FIELD], dtype=np.float64)
        if has_true:
            true_values = np.asarray(data[TRUE_DENOMINATOR_FIELD], dtype=np.float64)
            if true_values.shape != alias_values.shape or not np.allclose(true_values, alias_values, rtol=1.0e-12, atol=1.0e-12):
                raise ValueError(f"{source_path} contains conflicting true-denominator aliases")

        payload = {name: np.asarray(data[name]) for name in data.files if name != ALIAS_DENOMINATOR_FIELD}
        payload[TRUE_DENOMINATOR_FIELD] = alias_values
        normalized_path = tmpdir / f"{source_path.stem}.velocity_hessian_normalized.npz"
        _write_npz(normalized_path, payload)
        return normalized_path


def _build_raw_snapshot_archive(raw_path: Path, frame_index: int, tmpdir: Path) -> Path:
    data = _load_npz(raw_path)
    frame_count = _frame_count_from_raw_archive(data)
    if frame_index < 0 or frame_index >= frame_count:
        raise ValueError(f"frame {frame_index} is out of range for {raw_path} with {frame_count} frame(s)")

    payload = {name: _slice_for_frame(value, frame_index, frame_count) for name, value in data.items()}
    snapshot_path = tmpdir / f"{raw_path.stem}.frame{frame_index}.raw.npz"
    _write_npz(snapshot_path, payload)
    return snapshot_path


def _build_derived_frame_archive(raw_path: Path, frame_index: int, tmpdir: Path) -> Path:
    snapshot_path = _build_raw_snapshot_archive(raw_path, frame_index, tmpdir)
    derived_path = tmpdir / f"{raw_path.stem}.frame{frame_index}.derived.npz"
    args = argparse.Namespace(
        input=snapshot_path,
        output=derived_path,
        domain_length=None,
        beta_value=None,
        snapshot_index=None,
        allow_zero_pressure=False,
        include_velocity_hessian=True,
    )
    payload, _manifest = derived_archive._build_archive(args)
    derived_archive._write_npz_atomic(derived_path, payload)
    return derived_path


def _build_derived_snapshot_archive(derived_path: Path, frame_index: int, tmpdir: Path) -> Path:
    data = _load_npz(derived_path)
    frame_count = _frame_count_from_derived_archive(data)
    if frame_index < 0 or frame_index >= frame_count:
        raise ValueError(f"frame {frame_index} is out of range for {derived_path} with {frame_count} frame(s)")
    payload = {name: _slice_for_frame(value, frame_index, frame_count) for name, value in data.items()}
    snapshot_path = tmpdir / f"{derived_path.stem}.frame{frame_index}.derived.npz"
    _write_npz(snapshot_path, payload)
    return snapshot_path


def _auto_component_id_from_archive(path: Path) -> int:
    with np.load(path, allow_pickle=False) as data:
        if "lambda2" not in data:
            raise ValueError(f"{path} is missing lambda2 for automatic carrier selection")
        lambda2 = np.asarray(data["lambda2"], dtype=np.float64)
        beta = float(np.asarray(data["beta"]).item()) if "beta" in data and np.asarray(data["beta"]).shape == () else 0.0
    labels = _label_components(lambda2 <= beta)
    component_count = int(labels.max())
    if component_count <= 0:
        raise ValueError("automatic carrier selection found no components")
    sizes = np.bincount(labels.ravel())
    if sizes.size <= 1:
        raise ValueError("automatic carrier selection found no nonzero labels")
    return int(np.argmax(sizes[1:]) + 1)


def _run_korn_payload(
    source_path: Path,
    component_id: int | None,
    lambda2_band: float,
    strict: bool,
    *,
    tmpdir: Path | None = None,
    raw_input_path: Path | None = None,
    frame_index: int | None = None,
    layer_thickness_physical: float | None = None,
) -> dict[str, Any]:
    effective_path = source_path
    if raw_input_path is not None:
        if frame_index is None:
            raise ValueError("raw input path requires a frame index")
        if tmpdir is None:
            raise ValueError("temporary directory is required for raw input processing")
        effective_path = _build_derived_frame_archive(raw_input_path, frame_index, tmpdir)
    elif frame_index is not None:
        if tmpdir is None:
            raise ValueError("temporary directory is required for derived frame slicing")
        effective_path = _build_derived_snapshot_archive(source_path, frame_index, tmpdir)
    with np.load(effective_path, allow_pickle=False) as data:
        if ALIAS_DENOMINATOR_FIELD in data:
            if tmpdir is None:
                raise ValueError("temporary directory is required to normalize the denominator field")
            effective_path = _normalize_true_denominator_archive(effective_path, tmpdir)
        elif TRUE_DENOMINATOR_FIELD not in data:
            raise ValueError(
                f"{effective_path} does not contain the true denominator field {TRUE_DENOMINATOR_FIELD}"
            )
    if component_id is None:
        component_id = _auto_component_id_from_archive(effective_path)

    args = argparse.Namespace(
        input=effective_path,
        component_id=int(component_id),
        lambda2_band=float(lambda2_band),
        beta=None,
        layer_radius_cells=korn_diag.DEFAULT_LAYER_RADIUS_CELLS,
        layer_thickness_physical=layer_thickness_physical,
        strict=bool(strict),
        json=True,
        output=None,
    )
    payload = korn_diag._component_payload(args)
    payload["input"] = str(source_path)
    return payload


def _load_source_frames(input_path: Path) -> tuple[str, list[Path], int]:
    if input_path.is_dir():
        def frame_sort_key(path: Path) -> tuple[int, str]:
            match = FRAME_NUMBER_RE.search(path.stem)
            if match is not None:
                return int(match.group(1)), path.name
            return 10**12, path.name

        files = sorted(
            (path for path in input_path.iterdir() if path.is_file() and path.suffix.lower() == ".npz"),
            key=frame_sort_key,
        )
        if not files:
            raise ValueError(f"no .npz archives found in directory {input_path}")
        return "derived_dir", files, len(files)
    if not input_path.exists():
        raise FileNotFoundError(f"input path not found: {input_path}")
    if input_path.suffix.lower() != ".npz":
        raise ValueError("input must be a .npz archive or a directory of .npz archives")
    data = _load_npz(input_path)
    if _looks_like_derived_archive(data):
        return "derived_npz", [input_path], _frame_count_from_derived_archive(data)
    return "raw", [input_path], _frame_count_from_raw_archive(data)


def _process_frame(
    source_path: Path,
    frame_index: int,
    component_id: int | None,
    lambda2_band: float,
    strict: bool,
    input_mode: str,
    tmpdir: Path,
    layer_thickness_physical: float | None,
) -> dict[str, Any]:
    try:
        payload = _run_korn_payload(
            source_path,
            component_id,
            lambda2_band,
            strict,
            tmpdir=tmpdir,
            raw_input_path=source_path if input_mode == "raw" else None,
            frame_index=frame_index if input_mode in {"raw", "derived_npz"} else None,
            layer_thickness_physical=layer_thickness_physical,
        )
        payload.update(
            {
                "frame": int(frame_index),
                "carrier_id": int(payload.get("component_id", component_id)),
                "carrier_source_kind": "auto_largest_component" if component_id is None else input_mode,
                "source_path": str(source_path),
                "layer_thickness_physical_from_carrier": layer_thickness_physical,
                "boundary_samples": payload.get("boundary_cell_count"),
                "true_denominator_kind": payload.get("denominator_kind"),
                "min_g12": (payload.get("boundary_g12_stats") or {}).get("min")
                if isinstance(payload.get("boundary_g12_stats"), dict)
                else None,
                "rho_min": (payload.get("boundary_rho_stats") or {}).get("min")
                if isinstance(payload.get("boundary_rho_stats"), dict)
                else None,
                "rho_mean": (payload.get("boundary_rho_stats") or {}).get("mean")
                if isinstance(payload.get("boundary_rho_stats"), dict)
                else None,
                "grad_lambda2_max": (payload.get("boundary_grad_lambda2_stats") or {}).get("max")
                if isinstance(payload.get("boundary_grad_lambda2_stats"), dict)
                else None,
            }
        )
        return payload
    except Exception as exc:
        return {
            "script": SCRIPT_NAME,
            "contract": CONTRACT,
            "input": str(source_path),
            "frame": int(frame_index),
            "carrier_id": None if component_id is None else int(component_id),
            "carrier_source_kind": "auto_largest_component" if component_id is None else input_mode,
            "status": "missing_required_field",
            "strict": bool(strict),
            "lambda2_band": float(lambda2_band),
            "source_path": str(source_path),
            "warnings": [],
            "errors": [f"{type(exc).__name__}:{exc}"],
            "authority": {
                "candidate_only": True,
                "empirical_non_promoting": True,
                "truth_authority": False,
                "theorem_authority": False,
                "clay_authority": False,
                "runtime_authority": False,
                "promoted": False,
            },
        }


def _summarize_rows(rows: list[dict[str, Any]], available_frame_count: int, carrier_source: dict[str, Any], input_mode: str) -> dict[str, Any]:
    status_counts = Counter(str(row.get("status", "missing_required_field")) for row in rows)
    carrier_ids = sorted({int(row["carrier_id"]) for row in rows if row.get("carrier_id") is not None})
    ok_rows = [row for row in rows if str(row.get("status", "")) == "ok"]
    denominator_kinds = sorted(
        {str(row.get("denominator_kind")) for row in ok_rows if row.get("denominator_kind") is not None}
    )
    def finite_values(name: str) -> list[float]:
        values: list[float] = []
        for row in ok_rows:
            value = row.get(name)
            if value is None:
                continue
            number = float(value)
            if math.isfinite(number):
                values.append(number)
        return values

    c_true = finite_values("c_empirical_true")
    proxy_to_true = finite_values("denominator_proxy_to_true_ratio")
    min_g12 = finite_values("min_g12")
    rho_min = finite_values("rho_min")
    return {
        "available_frame_count": int(available_frame_count),
        "processed_frame_count": len(rows),
        "ok_row_count": len(ok_rows),
        "carrier_id_unique": carrier_ids,
        "carrier_stable": len(carrier_ids) <= 1,
        "denominator_kind_unique": denominator_kinds,
        "status_counts": dict(sorted(status_counts.items())),
        "carrier_source": carrier_source,
        "input_mode": input_mode,
        "c_empirical_true_min": min(c_true) if c_true else None,
        "c_empirical_true_mean": float(sum(c_true) / len(c_true)) if c_true else None,
        "c_empirical_true_max": max(c_true) if c_true else None,
        "denominator_proxy_to_true_ratio_min": min(proxy_to_true) if proxy_to_true else None,
        "denominator_proxy_to_true_ratio_mean": float(sum(proxy_to_true) / len(proxy_to_true)) if proxy_to_true else None,
        "denominator_proxy_to_true_ratio_max": max(proxy_to_true) if proxy_to_true else None,
        "min_g12_min": min(min_g12) if min_g12 else None,
        "rho_min_min": min(rho_min) if rho_min else None,
        "true_ratio_bounded_away_from_zero_empirical": bool(c_true and min(c_true) > 0.0),
    }


def _overall_status(rows: list[dict[str, Any]]) -> str:
    statuses = [str(row.get("status", "missing_required_field")) for row in rows]
    if not statuses:
        return "missing_required_field"
    if all(status == "ok" for status in statuses):
        return "ok"
    if any(status == "missing_required_field" for status in statuses):
        return "partial" if any(status == "ok" for status in statuses) else "missing_required_field"
    return "partial"


def _render_text(payload: dict[str, Any]) -> str:
    summary = payload.get("summary", {})
    lines = [
        f"status: {payload.get('status')}",
        f"input: {payload.get('input')}",
        f"source_mode: {payload.get('source_mode')}",
        f"carrier_source: {summary.get('carrier_source', {}).get('kind')}",
        f"frame_count: {payload.get('frame_count')}",
        f"carrier_id_unique: {summary.get('carrier_id_unique')}",
        f"denominator_kind_unique: {summary.get('denominator_kind_unique')}",
    ]
    rows = payload.get("rows", [])
    for row in rows[:5]:
        lines.append(
            f"frame {row.get('frame')}: carrier_id={row.get('carrier_id')} "
            f"status={row.get('status')} denominator_kind={row.get('denominator_kind')} "
            f"c_empirical_true={row.get('c_empirical_true')}"
        )
    if len(rows) > 5:
        lines.append(f"... {len(rows) - 5} more frames")
    warnings = payload.get("warnings", [])
    if warnings:
        lines.append(f"warnings: {len(warnings)}")
    errors = payload.get("errors", [])
    if errors:
        lines.append(f"errors: {len(errors)}")
    return "\n".join(lines)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument(
        "--input",
        type=Path,
        required=True,
        help="raw velocity/pressure .npz archive or directory of derived per-frame .npz archives",
    )
    parser.add_argument(
        "--carrier-timeseries-json",
        type=Path,
        default=None,
        help="existing carrier-timeseries JSON payload to source frame -> component ids",
    )
    parser.add_argument(
        "--carrier-pair",
        action="append",
        default=[],
        type=_parse_carrier_pair,
        metavar="FRAME:COMPONENT",
        help="explicit carrier selection pair; may be repeated",
    )
    parser.add_argument(
        "--component-map",
        default="",
        help="explicit frame:component comma list, e.g. 0:1,1:1,7:2",
    )
    parser.add_argument("--lambda2-band", type=_finite_nonnegative_float, default=DEFAULT_LAMBDA2_BAND)
    parser.add_argument("--output", type=Path, required=True, help="output JSON path")
    parser.add_argument("--json", action="store_true", help="emit deterministic JSON on stdout")
    parser.add_argument("--strict", action="store_true", help="fail closed when required metadata is absent")
    return parser.parse_args()


def _carrier_source_payload(args: argparse.Namespace) -> tuple[dict[int, int], dict[str, Any]]:
    if args.carrier_timeseries_json is not None:
        if args.carrier_pair or str(args.component_map).strip():
            raise ValueError("carrier-timeseries JSON is mutually exclusive with explicit carrier pairs")
        return _carrier_map_from_json(args.carrier_timeseries_json)
    explicit_pairs = list(args.carrier_pair)
    explicit_pairs.extend(CarrierSelection(frame=frame, component_id=component_id) for frame, component_id in _parse_component_map(args.component_map).items())
    if not explicit_pairs:
        return _carrier_map_auto()
    return _carrier_map_from_pairs(explicit_pairs)


def main() -> int:
    args = parse_args()
    payload: dict[str, Any] = {
        "script": SCRIPT_NAME,
        "contract": CONTRACT,
        "input": str(args.input),
        "lambda2_band": float(args.lambda2_band),
        "strict": bool(args.strict),
        "rows": [],
        "warnings": [],
        "errors": [],
        "authority": {
            "candidate_only": True,
            "empirical_non_promoting": True,
            "truth_authority": False,
            "theorem_authority": False,
            "clay_authority": False,
            "runtime_authority": False,
            "promoted": False,
        },
    }

    try:
        carrier_map, carrier_source = _carrier_source_payload(args)
        input_mode, source_paths, available_frame_count = _load_source_frames(args.input)
        selected_frames: list[tuple[int, int | None]]
        if carrier_map:
            selected_frames = sorted(carrier_map.items())
        else:
            selected_frames = [(frame, None) for frame in range(available_frame_count)]
        if input_mode in {"derived_dir", "derived_npz"} and any(frame >= available_frame_count for frame, _ in selected_frames):
            bad = min(frame for frame, _ in selected_frames if frame >= available_frame_count)
            raise ValueError(
                f"carrier selection references frame {bad}, but derived directory has only {available_frame_count} frame(s)"
            )
        if input_mode == "raw" and any(frame >= available_frame_count for frame, _ in selected_frames):
            bad = min(frame for frame, _ in selected_frames if frame >= available_frame_count)
            raise ValueError(
                f"carrier selection references frame {bad}, but raw archive has only {available_frame_count} frame(s)"
            )

        rows: list[dict[str, Any]] = []
        layer_thickness_by_frame = carrier_source.get("layer_thickness_physical_by_frame", {})
        if not isinstance(layer_thickness_by_frame, dict):
            layer_thickness_by_frame = {}
        with tempfile.TemporaryDirectory(prefix="ns-boundary-true-korn-") as tmp:
            tmpdir = Path(tmp)
            for frame, component_id in selected_frames:
                source_path = args.input if input_mode in {"raw", "derived_npz"} else source_paths[frame]
                layer_value = layer_thickness_by_frame.get(str(frame))
                row = _process_frame(
                    source_path,
                    frame,
                    component_id,
                    args.lambda2_band,
                    args.strict,
                    input_mode,
                    tmpdir,
                    None if layer_value is None else float(layer_value),
                )
                rows.append(row)

        payload["rows"] = rows
        payload["frame_count"] = len(rows)
        payload["available_frame_count"] = int(available_frame_count)
        payload["source_mode"] = input_mode
        payload["carrier_source"] = carrier_source
        payload["summary"] = _summarize_rows(rows, available_frame_count, carrier_source, input_mode)
        payload["warnings"] = sorted(
            {
                warning
                for row in rows
                for warning in row.get("warnings", [])
                if warning and isinstance(warning, str)
            }
        )
        payload["errors"] = sorted(
            {
                str(row.get("status"))
                for row in rows
                if str(row.get("status", "ok")) != "ok"
            }
        )
        payload["status"] = _overall_status(rows)
    except Exception as exc:
        payload["status"] = "missing_required_field"
        payload["errors"] = [f"{type(exc).__name__}:{exc}"]
        payload["warnings"] = []
        payload["rows"] = []
        payload["frame_count"] = 0
        payload["available_frame_count"] = 0
        payload["source_mode"] = None
        payload["carrier_source"] = None
        payload["summary"] = {
            "available_frame_count": 0,
            "processed_frame_count": 0,
            "ok_row_count": 0,
            "carrier_id_unique": [],
            "carrier_stable": True,
            "denominator_kind_unique": [],
            "status_counts": {},
            "carrier_source": None,
            "input_mode": None,
        }

    text = _json_text(payload)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(text + "\n", encoding="utf-8")
    if args.json:
        print(text)
    else:
        print(_render_text(payload))
    return 0 if payload.get("status") == "ok" else 1


if __name__ == "__main__":
    raise SystemExit(main())
