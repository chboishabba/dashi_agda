#!/usr/bin/env python3
"""Calc 5/F123 boundary absorption diagnostic.

This diagnostic consumes a derived NS boundary archive or materialized pairfield
NPZ and inspects the boundary-band damping quantity

    density := -2 * lambda3 * omega_e2_sq / g12^2

on the mask ``|lambda2| <= lambda2_band``.  If a component label field is
available, the analysis can be restricted to one label component via
``--component-id``.

The diagnostic is fail-closed: it produces a deterministic JSON payload with
status and reasons for any non-ok condition.  Optional positive-commutator
proxy comparisons can be requested by field name(s) and are included as
projections on the exact same analysis mask.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np


SCRIPT_NAME = "scripts/ns_boundary_f123_absorption_diagnostic.py"
CONTRACT = "ns_boundary_f123_absorption_diagnostic"
ROUTE_DECISION = "FAIL_CLOSED_F123_ABSORPTION_DIAGNOSTIC"
DEFAULT_LAMBDA2_BAND = 1.0e-3
DEFAULT_QUANTILES = (0.0, 0.1, 0.25, 0.5, 0.75, 0.9, 1.0)

OK_STATUS = "ok"
STATUS_INVALID = "invalid_input"
STATUS_MISSING = "missing_required_field"
STATUS_NO_BOUNDARY = "no_boundary_cells"
STATUS_NO_ANALYSIS = "no_analysis_cells"
STATUS_NO_VALID_DENSITY = "no_valid_density_values"


@dataclass(frozen=True)
class FieldBundle:
    lambda2: np.ndarray
    g12: np.ndarray
    lambda3: np.ndarray
    omega_e2_sq: np.ndarray
    labels: np.ndarray | None
    label_field: str | None
    boundary_mask: np.ndarray
    analysis_mask: np.ndarray
    lambda3_source: str
    lambda2_band: float
    grid_spacing: float | None
    domain_length: float | None
    scale_source: str | None
    component_id: int | None
    source: str


def _authority() -> dict[str, bool]:
    return {
        "candidate_only": True,
        "empirical_non_promoting": True,
        "truth_authority": False,
        "theorem_authority": False,
        "clay_authority": False,
        "runtime_authority": False,
        "promoted": False,
    }


def _json_text(payload: dict[str, Any]) -> str:
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _finite_nonnegative_float(value: Any) -> float:
    parsed = float(value)
    if not math.isfinite(parsed) or parsed < 0.0:
        raise argparse.ArgumentTypeError("value must be finite and nonnegative")
    return parsed


def _finite_probability(value: str) -> float:
    parsed = float(value)
    if not math.isfinite(parsed) or parsed < 0.0 or parsed > 1.0:
        raise argparse.ArgumentTypeError("quantile must be finite in [0,1]")
    return parsed


def _positive_int(value: str) -> int:
    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("value must be positive")
    return parsed


def _parse_frame(value: str | None) -> int | None:
    if value is None:
        return None
    parsed = int(value)
    if parsed < 0:
        raise argparse.ArgumentTypeError("frame must be nonnegative")
    return parsed


def _parse_proxy_names(values: list[str] | None) -> list[str]:
    out: list[str] = []
    for item in values or []:
        for part in item.split(","):
            name = part.strip()
            if name:
                out.append(name)
    # Stable dedupe.
    deduped: list[str] = []
    seen: set[str] = set()
    for name in out:
        if name in seen:
            continue
        deduped.append(name)
        seen.add(name)
    return deduped


def _load_npz(path: Path) -> dict[str, np.ndarray]:
    with np.load(path, allow_pickle=False) as data:
        payload = {name: np.asarray(data[name]) for name in data.files}

    if "meta_json" in payload:
        try:
            meta = json.loads(str(np.asarray(payload["meta_json"]).item()))
        except Exception as exc:  # pragma: no cover - defensive fallback.
            raise ValueError(f"meta_json in {path} could not be parsed: {exc}") from exc
        if isinstance(meta, dict):
            for key in ("domain_length", "grid_spacing", "N", "length", "axis_order"):
                if key not in payload and key in meta:
                    payload[key] = np.asarray(meta[key])
    return payload


def _extract_scalar_metadata(data: dict[str, np.ndarray], names: tuple[str, ...]) -> tuple[Any | None, str | None]:
    for key in names:
        if key not in data:
            continue
        value = np.asarray(data[key])
        if value.ndim == 0:
            scalar = value.item()
        elif value.ndim == 1 and value.size == 1:
            scalar = value[0]
        else:
            raise ValueError(f"{key} metadata must be scalar, got shape {value.shape!r}")

        if isinstance(scalar, np.ndarray):
            scalar = scalar.item()
        if isinstance(scalar, bytes):
            scalar = scalar.decode("utf-8")
        if isinstance(scalar, np.generic):
            scalar = scalar.item()
        return scalar, key
    return None, None


def _coerce_positive(value: Any, *, name: str) -> float | None:
    try:
        scalar = float(value)
    except Exception as exc:  # pragma: no cover - defensive.
        raise ValueError(f"{name} from metadata must be numeric: {exc}") from exc
    if not math.isfinite(scalar) or scalar <= 0.0:
        return None
    return scalar


def _coerce_nonnegative(value: Any, *, name: str) -> float | None:
    try:
        scalar = float(value)
    except Exception as exc:  # pragma: no cover - defensive.
        raise ValueError(f"{name} from metadata must be numeric: {exc}") from exc
    if not math.isfinite(scalar) or scalar < 0.0:
        return None
    return scalar


def _squeeze_field(name: str, raw: np.ndarray, frame: int | None) -> np.ndarray:
    arr = np.asarray(raw)
    if arr.ndim == 4:
        if frame is None:
            if int(arr.shape[0]) != 1:
                raise ValueError(
                    f"{name} has {int(arr.shape[0])} frames; pass --frame to select one"
                )
            arr = arr[0]
        else:
            if frame < 0 or frame >= int(arr.shape[0]):
                raise ValueError(f"{name} frame {frame} is out of range for {int(arr.shape[0])} frame(s)")
            arr = arr[frame]
    if arr.ndim != 3:
        raise ValueError(f"{name} must be rank-3 after frame selection, got {arr.shape!r}")
    return arr


def _load_label_field(
    data: dict[str, np.ndarray],
    lambda2: np.ndarray,
    frame: int | None,
    requested: str | None,
) -> tuple[np.ndarray | None, str | None, list[str]]:
    warnings: list[str] = []
    candidates = ("component_labels", "labels", "component_label")
    if requested is not None:
        candidates = (requested,)

    for name in candidates:
        if name not in data:
            continue
        labels = _squeeze_field(name, np.asarray(data[name]), frame).astype(np.int64)
        if labels.shape != lambda2.shape:
            raise ValueError(f"label field {name} shape {labels.shape!r} does not match lambda2")
        if np.any(labels < 0):
            raise ValueError(f"label field {name} contains negative values")
        return labels, name, warnings

    if requested is not None:
        warnings.append(f"requested_label_field_not_found:{requested}")
    return None, None, warnings


def _load_scale_metadata(data: dict[str, np.ndarray], shape: tuple[int, int, int]) -> tuple[float | None, float | None, str | None, list[str]]:
    warnings: list[str] = []
    n = float(shape[0])
    grid_spacing_raw, _ = _extract_scalar_metadata(data, ("grid_spacing",))
    domain_length_raw, _ = _extract_scalar_metadata(data, ("domain_length", "length"))
    n_raw, _ = _extract_scalar_metadata(data, ("N",))

    grid_spacing = None
    domain_length = None
    source: str | None = None

    if grid_spacing_raw is not None:
        grid_spacing = _coerce_positive(grid_spacing_raw, name="grid_spacing")
        if grid_spacing is None:
            warnings.append("grid_spacing_invalid")
        else:
            source = "grid_spacing"
            domain_length = grid_spacing * n
            if domain_length_raw is not None:
                dl = _coerce_nonnegative(domain_length_raw, name="domain_length")
                if dl is None:
                    warnings.append("domain_length_invalid")
                else:
                    if not math.isclose(float(dl), float(domain_length), rel_tol=1.0e-12, abs_tol=1.0e-12):
                        warnings.append("grid_spacing_domain_length_mismatch")
    elif domain_length_raw is not None:
        domain_length = _coerce_positive(domain_length_raw, name="domain_length")
        if domain_length is None:
            warnings.append("domain_length_invalid")
        else:
            source = "domain_length"
            grid_spacing = domain_length / n
    elif n_raw is not None:
        # Derive grid scale from N only when N and a cubic domain are present.
        try:
            n_scalar = int(float(np.asarray(n_raw).item()))
        except Exception:  # pragma: no cover
            n_scalar = None
        if n_scalar and int(n_scalar) == int(n) and n_scalar > 0:
            warnings.append("grid_spacing_domain_length_unavailable")
            source = "index_units"
        else:
            warnings.append("scale_unreliable_n_mismatch")
    else:
        source = "index_units"
    return grid_spacing, domain_length, source, warnings


def _finite_bool_all(arrays: list[tuple[str, np.ndarray]], warnings: list[str]) -> bool:
    for name, arr in arrays:
        if not np.all(np.isfinite(arr)):
            warnings.append(f"nonfinite_field:{name}")
            return False
    return True


def _make_lambda3(data: dict[str, np.ndarray], lambda2: np.ndarray, g12: np.ndarray, frame: int | None) -> tuple[np.ndarray, str]:
    if "lambda3" in data:
        return _squeeze_field("lambda3", np.asarray(data["lambda3"], dtype=np.float64), frame), "lambda3"
    return (np.asarray(g12, dtype=np.float64) - 2.0 * np.asarray(lambda2, dtype=np.float64), "derived_from_g12_minus_2_lambda2")


def _load_required_fields(
    path: Path,
    *,
    frame: int | None,
    lambda2_band: float,
    component_id: int | None,
    label_field: str | None,
) -> tuple[FieldBundle | None, list[str], list[str]]:
    warnings: list[str] = []
    errors: list[str] = []

    try:
        data = _load_npz(path)
    except FileNotFoundError as exc:
        return None, [f"input_missing:{path}"], []
    except Exception as exc:
        return None, [f"input_invalid:{exc}"], []

    required = ("lambda2", "g12", "omega_e2_sq")
    missing = [name for name in required if name not in data]
    if missing:
        return None, [f"missing_required_field:{name}" for name in missing], warnings

    try:
        lambda2 = _squeeze_field("lambda2", np.asarray(data["lambda2"], dtype=np.float64), frame)
        g12 = _squeeze_field("g12", np.asarray(data["g12"], dtype=np.float64), frame)
        omega_e2_sq = _squeeze_field("omega_e2_sq", np.asarray(data["omega_e2_sq"], dtype=np.float64), frame)
    except Exception as exc:
        return None, [f"field_unpack:{exc}"], warnings

    if lambda2.shape != g12.shape or lambda2.shape != omega_e2_sq.shape:
        return None, [f"shape_mismatch:{lambda2.shape!r},{g12.shape!r},{omega_e2_sq.shape!r}"], warnings

    if not _finite_bool_all(
        [("lambda2", lambda2), ("g12", g12), ("omega_e2_sq", omega_e2_sq)],
        warnings,
    ):
        return None, ["nonfinite_required_field"], warnings

    lambda3, lambda3_source = _make_lambda3(data, lambda2, g12, frame)
    if lambda3.shape != lambda2.shape:
        return None, [f"lambda3_shape_mismatch:{lambda3.shape!r},{lambda2.shape!r}"], warnings
    if not np.all(np.isfinite(lambda3)):
        return None, ["nonfinite_lambda3"], warnings

    labels, label_source, label_warnings = _load_label_field(data, lambda2, frame, label_field)
    warnings.extend(label_warnings)

    if labels is not None:
        labels = np.asarray(labels, dtype=np.int64)
        if np.any(labels < 0):
            return None, ["labels_negative_values"], warnings
        if component_id is not None:
            if component_id <= 0:
                return None, ["component_id_nonpositive"], warnings
            if not np.any(labels == component_id):
                return None, [f"component_id_not_found:{component_id}"], warnings
    elif component_id is not None:
        return None, ["component_id_requested_without_labels"], warnings

    if np.any(omega_e2_sq < 0.0):
        warnings.append("omega_e2_sq_has_negative_values")

    boundary_mask = np.abs(lambda2) <= float(lambda2_band)
    boundary_cells = int(np.count_nonzero(boundary_mask))
    if boundary_cells == 0:
        return None, ["no_boundary_cells"], warnings

    if labels is not None and component_id is not None:
        analysis_mask = np.asarray(boundary_mask & (labels == component_id), dtype=bool)
    else:
        analysis_mask = np.asarray(boundary_mask, dtype=bool)

    if not np.any(analysis_mask):
        return None, ["no_analysis_cells"], warnings

    if np.any(omega_e2_sq[analysis_mask] < 0.0):
        warnings.append("omega_e2_sq_negative_in_analysis")

    grid_spacing, domain_length, scale_source, scale_warnings = _load_scale_metadata(data, lambda2.shape)
    warnings.extend(scale_warnings)

    return (
        FieldBundle(
            lambda2=lambda2,
            g12=g12,
            lambda3=lambda3,
            omega_e2_sq=omega_e2_sq,
            labels=labels,
            label_field=label_source,
            boundary_mask=np.asarray(boundary_mask, dtype=bool),
            analysis_mask=analysis_mask,
            lambda3_source=lambda3_source,
            lambda2_band=float(lambda2_band),
            grid_spacing=None if grid_spacing is None else float(grid_spacing),
            domain_length=None if domain_length is None else float(domain_length),
            scale_source=scale_source,
            component_id=component_id,
            source=str(path),
        ),
        [],
        warnings,
    )


def _quantile_payload(values: np.ndarray, quantiles: list[float]) -> dict[str, Any]:
    arr = np.asarray(values, dtype=np.float64)
    if arr.size == 0:
        return {
            "cell_count": 0,
            "min": None,
            "mean": None,
            "max": None,
            "sum": None,
            "quantiles": [],
        }
    return {
        "cell_count": int(arr.size),
        "min": float(np.min(arr)),
        "mean": float(np.mean(arr)),
        "max": float(np.max(arr)),
        "sum": float(np.sum(arr)),
        "quantiles": [
            {"q": float(q), "value": float(np.quantile(arr, q))}
            for q in quantiles
        ],
    }


def _proxy_compare(
    *,
    name: str,
    proxy_raw: np.ndarray,
    density_abs: np.ndarray,
    analysis_mask: np.ndarray,
    quantiles: list[float],
    tolerance: float,
) -> tuple[dict[str, Any], list[str]]:
    payload: dict[str, Any] = {
        "proxy": name,
        "status": OK_STATUS,
        "proxy_count": int(proxy_raw.size),
        "proxy_stats": _quantile_payload([], quantiles),
        "ratio_sum": None,
        "ratio_quantiles": [],
        "ratio_mean": None,
        "ratio_max": None,
        "dominance_flags": {
            "pointwise_comparison_available": False,
            "all_density_abs_leq_proxy": False,
            "max_ratio_leq_one_plus_tolerance": False,
            "fraction_pointwise_leq": None,
            "all_proxy_nonnegative": False,
        },
    }
    warnings: list[str] = []

    proxy = np.asarray(proxy_raw, dtype=np.float64)
    if proxy.shape != analysis_mask.shape:
        payload["status"] = "proxy_shape_mismatch"
        return payload, warnings
    proxy_sel = proxy[analysis_mask]
    payload["proxy_stats"] = _quantile_payload(proxy_sel, quantiles)
    payload["proxy_count"] = int(proxy_sel.size)
    if not np.all(np.isfinite(proxy_sel)):
        payload["status"] = "proxy_nonfinite"
        return payload, warnings

    all_nonnegative = bool(np.all(proxy_sel >= 0.0))
    if not all_nonnegative:
        warnings.append(f"proxy_has_negative_values:{name}")

    if proxy_sel.size == 0:
        payload["status"] = "proxy_empty"
        return payload, warnings

    positive = proxy_sel > 0.0
    payload["dominance_flags"]["all_proxy_nonnegative"] = all_nonnegative
    payload["dominance_flags"]["pointwise_comparison_available"] = bool(np.any(positive))
    if not np.any(positive):
        return payload, warnings

    density_sel = density_abs
    if density_sel.size != proxy_sel.size:
        payload["status"] = "proxy_selection_mismatch"
        return payload, warnings

    ratio = density_sel[positive] / proxy_sel[positive]
    if not np.all(np.isfinite(ratio)):
        payload["status"] = "proxy_ratio_nonfinite"
        payload["ratio_quantiles"] = []
        return payload, warnings

    payload["ratio_quantiles"] = [{"q": float(q), "value": float(np.quantile(ratio, q))} for q in quantiles]
    payload["ratio_mean"] = float(np.mean(ratio))
    payload["ratio_max"] = float(np.max(ratio))

    sum_proxy = float(np.sum(proxy_sel[positive]))
    if sum_proxy > 0.0:
        payload["ratio_sum"] = float(np.sum(density_sel) / sum_proxy)

    payload["dominance_flags"].update(
        {
            "all_density_abs_leq_proxy": bool(np.all(density_sel[positive] <= proxy_sel[positive] + tolerance)),
            "max_ratio_leq_one_plus_tolerance": float(np.max(ratio)) <= 1.0 + tolerance,
            "fraction_pointwise_leq": float(np.mean(density_sel[positive] <= proxy_sel[positive] + tolerance)),
        }
    )
    return payload, warnings


def _comparison_summary(proxy_payloads: list[dict[str, Any]], damping_abs_sum: float) -> dict[str, Any]:
    available = [item for item in proxy_payloads if item.get("status") == OK_STATUS]
    if not available:
        return {
            "proxy_available": False,
            "proxy_count": 0,
            "dominates_any_pointwise": False,
            "dominates_all_pointwise": False,
            "min_ratio_sum": None,
            "max_ratio_sum": None,
            "damping_sum_ratio_reference": None,
        }

    ratio_summaries = [float(item["ratio_sum"]) for item in available if item.get("ratio_sum") is not None]
    pointwise_dom = [bool(item.get("dominance_flags", {}).get("max_ratio_leq_one_plus_tolerance")) for item in available]

    return {
        "proxy_available": True,
        "proxy_count": int(len(available)),
        "dominates_any_pointwise": bool(any(pointwise_dom)),
        "dominates_all_pointwise": bool(pointwise_dom and all(pointwise_dom)),
        "min_ratio_sum": None if not ratio_summaries else float(min(ratio_summaries)),
        "max_ratio_sum": None if not ratio_summaries else float(max(ratio_summaries)),
        "damping_sum_ratio_reference": float(damping_abs_sum),
    }


def _validate_args(args: argparse.Namespace) -> list[str]:
    errors: list[str] = []
    if not math.isfinite(args.lambda2_band) or args.lambda2_band < 0.0:
        errors.append("lambda2_band must be finite and nonnegative")
    if not args.density_quantiles:
        errors.append("density_quantiles must be non-empty")
    if any((q < 0.0 or q > 1.0) for q in args.density_quantiles):
        errors.append("density_quantiles must be in [0,1]")
    if not args.proxy_quantiles:
        errors.append("proxy_quantiles must be non-empty")
    if any((q < 0.0 or q > 1.0) for q in args.proxy_quantiles):
        errors.append("proxy_quantiles must be in [0,1]")
    if args.compare_tolerance < 0.0 or not math.isfinite(args.compare_tolerance):
        errors.append("compare_tolerance must be finite and nonnegative")
    return errors


def _analysis_payload(bundle: FieldBundle, proxy_names: list[str], args: argparse.Namespace) -> tuple[dict[str, Any], list[str], list[str], str]:
    warnings: list[str] = []
    errors: list[str] = []

    payload: dict[str, Any] = {
        "script": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "input": bundle.source,
        "input_shape": [int(v) for v in bundle.lambda2.shape],
        "shape": [int(v) for v in bundle.lambda2.shape],
        "status": OK_STATUS,
        "warnings": [],
        "errors": [],
        "authority": _authority(),
        "O": "Emit a deterministic empirical F123 boundary-band absorption diagnostic from NS-derived or pairfield NPZ inputs.",
        "R": "Compute |lambda2|-band density and compare it against configured positive-commutator proxy channels.",
        "C": SCRIPT_NAME,
        "S": "Load required fields, form analysis masks, compute finite damping density and optional proxy dominance ratios.",
        "L": "Status is ok only when boundary+component analysis cells exist and contain at least one finite damping sample.",
        "P": ROUTE_DECISION,
        "G": "No analytic theorem, Clay theorem, or route promotion is claimed by this diagnostic.",
        "F": "Fail-closed: missing required fields, empty analysis masks, non-finite core fields, or unavailable requested proxy fields produce non-ok status.",
        "lambda2_band": float(bundle.lambda2_band),
        "lambda3_source": bundle.lambda3_source,
        "label_field": bundle.label_field,
        "component_id": bundle.component_id,
        "boundary_cell_count": int(np.count_nonzero(bundle.boundary_mask)),
        "analysis_mask_cell_count": int(np.count_nonzero(bundle.analysis_mask)),
        "grid_spacing": None if bundle.grid_spacing is None else float(bundle.grid_spacing),
        "domain_length": None if bundle.domain_length is None else float(bundle.domain_length),
        "scale_source": bundle.scale_source,
    }

    if bundle.labels is not None:
        payload["labels_cell_count"] = int(np.count_nonzero(bundle.labels))
        payload["labels_source"] = bundle.label_field
        payload["component_mask_applied"] = bool(bundle.component_id is not None)

    g12_sq = bundle.g12 * bundle.g12
    finite_denom_mask = g12_sq > 0.0
    valid_mask = bundle.analysis_mask & np.isfinite(bundle.lambda3) & np.isfinite(bundle.omega_e2_sq) & finite_denom_mask
    if not np.any(bundle.analysis_mask & np.isfinite(bundle.lambda3)):
        payload["warnings"].append("no_finite_lambda3_in_analysis")
    if not np.any(bundle.analysis_mask & np.isfinite(bundle.omega_e2_sq)):
        payload["warnings"].append("no_finite_omega_e2_sq_in_analysis")

    if not np.any(valid_mask):
        payload["status"] = STATUS_NO_VALID_DENSITY
        payload["g12_zero_or_nonpositive_cells"] = int(np.count_nonzero(bundle.analysis_mask & (~finite_denom_mask)))
        payload["errors"] = ["no_valid_density_values"]
        payload["warnings"] = sorted(set(payload["warnings"]))
        return payload, warnings, errors, payload["status"]

    density = np.empty(bundle.lambda2.shape, dtype=np.float64)
    density[:] = np.nan
    density[valid_mask] = (-2.0 * bundle.lambda3[valid_mask] * bundle.omega_e2_sq[valid_mask]) / g12_sq[valid_mask]

    density_valid = np.asarray(density[valid_mask], dtype=np.float64)
    density_abs = np.abs(density_valid)

    payload["selected_density_cells"] = int(density_valid.size)
    payload["damping_sum_signed"] = float(np.sum(density_valid))
    payload["damping_sum_abs"] = float(np.sum(density_abs))
    payload["g12_nonpositive_in_analysis"] = int(np.count_nonzero(bundle.analysis_mask & (~finite_denom_mask)))
    payload["g12_zero_or_nonpositive_cells"] = payload["g12_nonpositive_in_analysis"]
    payload["density_stats"] = _quantile_payload(density_valid, args.density_quantiles)
    payload["abs_damping_stats"] = _quantile_payload(density_abs, args.density_quantiles)

    if not np.all(np.isfinite(density_valid)):
        payload["status"] = STATUS_NO_VALID_DENSITY
        errors.append("nonfinite_density")

    if not np.all(np.isfinite(density_abs)):
        payload["status"] = STATUS_NO_VALID_DENSITY
        errors.append("nonfinite_abs_damping")

    proxy_payloads: list[dict[str, Any]] = []
    if not proxy_names:
        warnings.append("no_positive_commutator_fields_configured")

    for name in proxy_names:
        try:
            with np.load(bundle.source, allow_pickle=False) as data:
                if name not in data:
                    proxy_payload = {
                        "proxy": name,
                        "status": STATUS_MISSING,
                        "proxy_count": 0,
                        "proxy_stats": _quantile_payload(np.array([], dtype=np.float64), args.proxy_quantiles),
                        "ratio_sum": None,
                        "ratio_quantiles": [],
                        "ratio_mean": None,
                        "ratio_max": None,
                        "dominance_flags": {},
                    }
                    warnings.append(f"proxy_missing:{name}")
                    payload["status"] = STATUS_MISSING
                    proxy_payloads.append(proxy_payload)
                    continue

                proxy_raw = np.asarray(data[name], dtype=np.float64)
            proxy = _squeeze_field(name, proxy_raw, args.frame)
            proxy_sel = proxy[bundle.analysis_mask]
            comp, proxy_warnings = _compare_proxy_field(
                name=name,
                proxy=proxy,
                density_abs=density_abs,
                analysis_mask=valid_mask,
                quantiles=args.proxy_quantiles,
                tolerance=args.compare_tolerance,
            )
            if comp.get("status") != OK_STATUS:
                payload["status"] = STATUS_MISSING
            warnings.extend(proxy_warnings)
            proxy_payloads.append(comp)
        except ValueError as exc:
            payload["status"] = STATUS_INVALID
            errors.append(f"proxy_field_invalid:{name}:{exc}")
            proxy_payloads.append(
                {
                    "proxy": name,
                    "status": "proxy_invalid",
                    "proxy_count": 0,
                    "proxy_stats": _quantile_payload(np.array([], dtype=np.float64), args.proxy_quantiles),
                    "ratio_sum": None,
                    "ratio_quantiles": [],
                    "ratio_mean": None,
                    "ratio_max": None,
                    "dominance_flags": {},
                }
            )

    payload["proxy_fields_requested"] = proxy_names
    payload["proxy_comparisons"] = proxy_payloads
    payload["dominance"] = _comparison_summary(proxy_payloads, float(np.sum(density_abs)))
    payload["dominance_flags"] = {
        "any_pointwise_dominance": payload["dominance"].get("dominates_any_pointwise", False),
        "all_pointwise_dominance": payload["dominance"].get("dominates_all_pointwise", False),
        "proxy_available": payload["dominance"].get("proxy_available", False),
    }

    if payload["status"] == OK_STATUS and errors:
        payload["status"] = STATUS_INVALID
    if payload["status"] == OK_STATUS and payload["dominance"]["proxy_available"] and not payload["dominance"]["dominates_all_pointwise"]:
        # Keep non-ok as an explicit signal of incomplete pointwise dominance.
        payload["status"] = "partial_pointwise_dominance"
    payload["errors"] = sorted(set(errors))
    payload["warnings"] = sorted(set(warnings + list(payload.get("warnings") or [])))
    if payload["status"] == OK_STATUS and payload.get("warnings"):
        # Non-fatal: keep warning-only status only for informational output.
        payload["status"] = payload["status"]
    return payload, payload["warnings"], payload["errors"], payload["status"]


def _compare_proxy_field(
    *,
    name: str,
    proxy: np.ndarray,
    density_abs: np.ndarray,
    analysis_mask: np.ndarray,
    quantiles: list[float],
    tolerance: float,
) -> tuple[dict[str, Any], list[str]]:
    return _proxy_compare(
        name=name,
        proxy_raw=np.asarray(proxy, dtype=np.float64),
        density_abs=density_abs,
        analysis_mask=analysis_mask,
        quantiles=quantiles,
        tolerance=tolerance,
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", required=True, type=Path, help="Derived tensor NPZ or materialized pairfield NPZ")
    parser.add_argument("--lambda2-band", type=_finite_nonnegative_float, default=DEFAULT_LAMBDA2_BAND)
    parser.add_argument("--frame", type=_parse_frame, default=None, help="Frame index for 4D archives")
    parser.add_argument("--component-id", type=_positive_int, default=None, help="Optional component id from a label field")
    parser.add_argument("--label-field", type=str, default=None, help="Optional explicit label field")
    parser.add_argument(
        "--positive-commutator-field",
        action="append",
        default=[],
        help="Add positive-commutator proxy field by name (repeatable).",
    )
    parser.add_argument(
        "--positive-commutator-fields",
        type=str,
        default=None,
        help="Comma-separated positive-commutator proxy field names.",
    )
    parser.add_argument(
        "--density-quantiles",
        type=_finite_probability,
        nargs="+",
        default=list(DEFAULT_QUANTILES),
        help="Quantiles to report for density and |density|",
    )
    parser.add_argument(
        "--proxy-quantiles",
        type=_finite_probability,
        nargs="+",
        default=list(DEFAULT_QUANTILES),
        help="Quantiles to report for proxy comparisons",
    )
    parser.add_argument(
        "--compare-tolerance",
        type=float,
        default=0.0,
        help="Tolerance for dominance comparisons against proxies",
    )
    parser.add_argument("--json", action="store_true", help="Emit JSON")
    parser.add_argument("--output", type=Path, default=None, help="Write JSON output to this file")
    return parser.parse_args()


def _error_payload(args: argparse.Namespace, status: str, errors: list[str]) -> dict[str, Any]:
    return {
        "script": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "input": str(args.input),
        "status": status,
        "errors": sorted(set(errors)),
        "warnings": [],
        "authority": _authority(),
        "O": "Emit a deterministic empirical F123 boundary-band absorption diagnostic from NS-derived or pairfield NPZ inputs.",
        "R": "Compute |lambda2|-band density and compare against configured positive-commutator proxy channels.",
        "C": SCRIPT_NAME,
        "S": "Validate CLI and required fields before analysis.",
        "L": "Status is non-ok when arguments fail validation or required fields cannot be loaded.",
        "P": ROUTE_DECISION,
        "G": "No analytic theorem, Clay theorem, or route promotion is claimed by this diagnostic.",
        "F": "Fail-closed by design; any validation or loading issue marks the diagnostic non-ok.",
    }


def _render_text(payload: dict[str, Any]) -> str:
    lines = [
        f"status: {payload.get('status')}",
        f"input: {payload.get('input')}",
        f"boundary_cell_count: {payload.get('boundary_cell_count', 0)}",
        f"analysis_mask_cell_count: {payload.get('analysis_mask_cell_count', 0)}",
        f"selected_density_cells: {payload.get('selected_density_cells', 0)}",
        f"damping_sum_abs: {payload.get('damping_sum_abs')}",
    ]
    if payload.get("warnings"):
        lines.append("warnings: " + ",".join(payload["warnings"]))
    if payload.get("errors"):
        lines.append("errors: " + ",".join(payload["errors"]))
    if "dominance" in payload and payload.get("dominance"):
        lines.append("dominance: " + json.dumps(payload["dominance"], sort_keys=True, separators=(",", ":")))
    return "\n".join(lines)


def main() -> int:
    args = parse_args()

    arg_errors = _validate_args(args)
    if arg_errors:
        payload = _error_payload(args, STATUS_INVALID, arg_errors)
        if args.output is not None:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(_json_text(payload) + "\n", encoding="utf-8")
        if args.json:
            print(_json_text(payload))
        else:
            print(_render_text(payload))
        return 1

    density_q = sorted(set(float(q) for q in args.density_quantiles))
    proxy_q = sorted(set(float(q) for q in args.proxy_quantiles))
    args.density_quantiles = density_q
    args.proxy_quantiles = proxy_q

    proxy_names = _parse_proxy_names(args.positive_commutator_field)
    if args.positive_commutator_fields:
        proxy_names.extend(_parse_proxy_names([args.positive_commutator_fields]))
    # Stable dedupe and deterministic order.
    deduped_proxy_names: list[str] = []
    seen_proxy: set[str] = set()
    for name in proxy_names:
        if name in seen_proxy:
            continue
        deduped_proxy_names.append(name)
        seen_proxy.add(name)

    bundle, load_errors, load_warnings = _load_required_fields(
        args.input,
        frame=args.frame,
        lambda2_band=args.lambda2_band,
        component_id=args.component_id,
        label_field=args.label_field,
    )

    if bundle is None:
        payload = _error_payload(args, STATUS_MISSING, load_errors)
        if load_warnings:
            payload["warnings"] = sorted(set(load_warnings))
        if args.output is not None:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(_json_text(payload) + "\n", encoding="utf-8")
        if args.json:
            print(_json_text(payload))
        else:
            print(_render_text(payload))
        return 1

    payload, warnings, errors, final_status = _analysis_payload(bundle, deduped_proxy_names, args)
    payload["status"] = final_status
    payload["warnings"] = sorted(set(payload.get("warnings", []) + warnings))
    payload["errors"] = sorted(set(payload.get("errors", []) + errors))

    if load_warnings:
        payload["warnings"] = sorted(set(payload["warnings"]) | set(load_warnings))

    # Canonicalize proxy payloads if present.
    if "proxy_comparisons" in payload:
        payload["proxy_fields_requested"] = deduped_proxy_names

    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(_json_text(payload) + "\n", encoding="utf-8")

    if args.json:
        print(_json_text(payload))
    else:
        print(_render_text(payload))

    return 0 if payload["status"] == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
