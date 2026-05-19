#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

FAMILY_CROSSWALK_PATH = Path(__file__).with_name("hepdata_family_crosswalk.json")


def _to_bool(raw: str) -> bool | None:
    value = raw.strip().lower()
    if value in {"1", "true", "t", "yes", "y", "on"}:
        return True
    if value in {"0", "false", "f", "no", "n", "off"}:
        return False
    return None


def _coerce_scalar(raw: str) -> str | float | int | bool | None:
    text = (raw or "").strip()
    if not text:
        return None
    if text.lower() in {"none", "null", "nan", "na", "n/a"}:
        return None

    bool_value = _to_bool(text)
    if bool_value is not None:
        return bool_value

    try:
        value = float(text)
    except ValueError:
        return text

    if value.is_integer():
        return int(value)
    return value


def _load_csv(path: Path) -> tuple[list[str], list[dict[str, str]]]:
    with path.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        rows = list(reader)
    header = list(reader.fieldnames or [])
    return header, rows


def _load_json(path: Path) -> dict[str, Any]:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def _coerce_row(row: dict[str, str]) -> dict[str, Any]:
    return {key: _coerce_scalar(value) for key, value in row.items()}


def load_family_crosswalk(path: Path = FAMILY_CROSSWALK_PATH) -> dict[str, Any]:
    if not path.exists():
        return {"schema_version": "missing", "families": {}}

    payload = _load_json(path)
    if not isinstance(payload, dict):
        raise ValueError("family crosswalk must decode to a JSON object")
    families = payload.get("families", {})
    if not isinstance(families, dict):
        raise ValueError("family crosswalk must contain a 'families' object")
    return payload


def build_default_family_spec(family: str) -> dict[str, Any]:
    return {
        "canonical_family": family,
        "measurement": {
            "npz": family,
            "lens_family": family,
        },
        "metrics": family,
        "timeseries": family,
        "certification_labels": [family],
        "aliases": [],
        "resolution": "implicit-exact",
    }


def resolve_family_spec(crosswalk: dict[str, Any], family: str) -> dict[str, Any]:
    families = crosswalk.get("families", {})
    if not isinstance(families, dict):
        return build_default_family_spec(family)

    if family in families and isinstance(families[family], dict):
        spec = dict(families[family])
        spec.setdefault("canonical_family", family)
        spec.setdefault("resolution", "crosswalk-exact")
        return spec

    for canonical, raw_spec in families.items():
        if not isinstance(raw_spec, dict):
            continue
        aliases = raw_spec.get("aliases", [])
        if isinstance(aliases, list) and family in aliases:
            spec = dict(raw_spec)
            spec.setdefault("canonical_family", canonical)
            spec.setdefault("resolution", "crosswalk-alias")
            return spec

    return build_default_family_spec(family)


def resolve_dashitest_root(path: Path) -> Path:
    for candidate in (path, *path.parents):
        if candidate.name in {"dashifine", "dashitest"}:
            return candidate
    return path


def resolve_data_root(path: Path) -> Path:
    """
    Normalize historical layout:
    ../dashitest typically stores all hepdata outputs under
    ../dashitest/dashifine, while some callers may already pass that
    subdirectory directly.
    """
    if path.name == "dashifine":
        return path
    if path.name == "dashitest":
        candidate = path / "dashifine"
        if candidate.exists():
            return candidate
        return path
    if path.parent.name == "dashitest" and (path.parent / "dashifine").exists():
        return path.parent / "dashifine"
    if path.name in {"hepdata_dashi_native", "hepdata_beta_dashboard_out", "hepdata_lyapunov_test_out", "hepdata_lyapunov_test_out_new", "hepdata_lyapunov_test_out_all", "hepdata_npz", "hepdata_npz_all", "hepdata_to_dashi", "hepdata_to_dashi_new", "hepdata_to_dashi_all"}:
        return path
    if path.parent.name == "dashifine":
        return path.parent
    return path


def parse_timeseries(
    path: Path,
    family_filter: str | None = None,
    family_filters: list[str] | None = None,
) -> dict[str, Any]:
    if not path.exists():
        return {"status": "missing", "path": str(path), "rows": []}

    header, rows = _load_csv(path)
    active_filters = [value for value in (family_filters or ([family_filter] if family_filter else [])) if value]
    filtered = rows
    if active_filters:
        accepted = set(active_filters)
        filtered = [row for row in rows if row.get("label") in accepted]
    parsed = [_coerce_row(row) for row in filtered]
    return {
        "status": "ok",
        "path": str(path),
        "columns": header,
        "row_count": len(parsed),
        "rows": parsed,
    }


def parse_metrics(
    path: Path,
    family_filter: str | None = None,
    family_filters: list[str] | None = None,
) -> dict[str, Any]:
    if not path.exists():
        return {"status": "missing", "path": str(path), "rows": []}

    header, rows = _load_csv(path)
    filtered = rows
    active_filters = [value for value in (family_filters or ([family_filter] if family_filter else [])) if value]
    if any(column == "label" for column in header) and active_filters:
        accepted = set(active_filters)
        filtered = [row for row in rows if row.get("label") in accepted]

    parsed = [_coerce_row(row) for row in filtered]
    return {
        "status": "ok",
        "path": str(path),
        "columns": header,
        "row_count": len(parsed),
        "rows": parsed,
        "summary_last_row": parsed[-1] if parsed else None,
    }


def parse_meta(path: Path) -> dict[str, Any]:
    output: dict[str, Any] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        if "=" not in line:
            continue
        key, value = line.split("=", 1)
        output[key.strip()] = _coerce_scalar(value)
    return output


def parse_measurement(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {"status": "missing", "path": str(path)}
    if path.suffix == ".npz":
        try:
            import numpy as np  # type: ignore

            payload = np.load(path, allow_pickle=True)
            x = [float(value) for value in payload["x"].tolist()]
            y = [float(value) for value in payload["y"].tolist()]
            cov = payload["cov"].tolist()
            output: dict[str, Any] = {
                "status": "ok",
                "path": str(path),
                "kind": "npz",
                "field_status": {
                    "x": "ok",
                    "y": "ok",
                    "cov": "ok",
                },
                "row_count": len(x),
                "x": x,
                "y": y,
                "cov": [[float(value) for value in row] for row in cov],
            }
            if "name" in payload:
                output["name"] = str(payload["name"])
            return output
        except Exception as err:  # pragma: no cover - defensive adapter branch
            return {"status": "error", "path": str(path), "error": str(err)}

    header, rows = _load_csv(path)
    return {
        "status": "ok",
        "kind": "csv",
        "path": str(path),
        "field_status": {
            "x": "missing",
            "y": "missing",
            "cov": "missing",
        },
        "columns": header,
        "rows": [_coerce_row(row) for row in rows],
        "row_count": len(rows),
    }


def load_family_measurement(
    context_root: Path,
    family: str,
    family_spec: dict[str, Any] | None = None,
) -> dict[str, Any] | None:
    measurement_spec = family_spec.get("measurement", {}) if isinstance(family_spec, dict) else {}
    npz_name = measurement_spec.get("npz", family) if isinstance(measurement_spec, dict) else family
    lens_family = (
        measurement_spec.get("lens_family", family)
        if isinstance(measurement_spec, dict)
        else family
    )

    for root_name in ("hepdata_npz_all", "hepdata_npz"):
        if not npz_name:
            continue
        npz_path = context_root / root_name / f"{npz_name}.npz"
        if npz_path.exists():
            output = parse_measurement(npz_path)
            output["source_dir"] = str(context_root / root_name)
            return output

    for root_name in ("hepdata_to_dashi_new", "hepdata_to_dashi_all", "hepdata_to_dashi"):
        if not lens_family:
            continue
        lens_dir = context_root / root_name / str(lens_family)
        csv_path = lens_dir / "lenses_continuous.csv"
        if csv_path.exists():
            output = parse_measurement(csv_path)
            if output["status"] == "ok":
                output["source_dir"] = str(lens_dir)
                meta_path = lens_dir / "meta.txt"
                if meta_path.exists():
                    output["meta"] = parse_meta(meta_path)
                return output

    return {
        "status": "missing",
        "family": family,
        "field_status": {
            "x": "missing",
            "y": "missing",
            "cov": "missing",
        },
        "notes": ["no lenses_continuous.csv or npz found for family"],
    }


def pick_timeseries_root(context_root: Path) -> Path | None:
    for variant in ("hepdata_lyapunov_test_out", "hepdata_lyapunov_test_out_new", "hepdata_lyapunov_test_out_all"):
        candidate = context_root / variant / "per_label_timeseries.csv"
        if candidate.exists():
            return candidate
    return None


def pick_certification(
    context_root: Path,
    family: str | None = None,
    certification_labels: list[str] | None = None,
    explicit: Path | None = None,
) -> dict[str, Any] | None:
    if explicit is not None:
        return {
            "selected": "explicit",
            "path": str(explicit),
            "value": _load_json(explicit),
        }

    if family is None:
        for variant in ("hepdata_lyapunov_test_out", "hepdata_lyapunov_test_out_new", "hepdata_lyapunov_test_out_all"):
            path = context_root / variant / "overall_certification.json"
            if path.exists():
                return {
                    "selected": variant,
                    "path": str(path),
                    "value": _load_json(path),
                }
        return None

    accepted_labels = set(certification_labels or ([family] if family else []))
    for variant in ("hepdata_lyapunov_test_out_new", "hepdata_lyapunov_test_out_all", "hepdata_lyapunov_test_out"):
        path = context_root / variant / "overall_certification.json"
        if not path.exists():
            continue
        value = _load_json(path)
        labels = value.get("labels")
        if isinstance(labels, list) and any(label in labels for label in accepted_labels):
            return {"selected": variant, "path": str(path), "value": value}
    return None


def infer_family_names(context_root: Path, crosswalk: dict[str, Any] | None = None) -> list[str]:
    families: set[str] = set()

    if isinstance(crosswalk, dict):
        crosswalk_families = crosswalk.get("families", {})
        if isinstance(crosswalk_families, dict):
            families.update(str(name) for name in crosswalk_families.keys())

    metrics_root = context_root / "hepdata_dashi_native"
    if metrics_root.exists():
        for metrics_path in metrics_root.glob("*_dashi_native_metrics.csv"):
            families.add(metrics_path.stem.removesuffix("_dashi_native_metrics"))

    for summary_path in (
        context_root / "hepdata_beta_dashboard_out" / "summary.csv",
        context_root / "hepdata_beta_dashboard_out" / "flags.csv",
    ):
        if not summary_path.exists():
            continue
        try:
            _, rows = _load_csv(summary_path)
            families.update(row.get("label", "") for row in rows if row.get("label"))
        except Exception:
            continue

    return sorted(families)


def build_family_payload(
    context_root: Path,
    family: str,
    family_spec: dict[str, Any],
    metrics_path_override: Path | None,
    timeseries_path_override: Path | None,
    cert_path_override: Path | None,
) -> dict[str, Any]:
    canonical_family = str(family_spec.get("canonical_family", family))
    metrics_family = str(family_spec.get("metrics", canonical_family))
    timeseries_family = str(family_spec.get("timeseries", canonical_family))
    certification_labels = family_spec.get("certification_labels", [canonical_family])
    if not isinstance(certification_labels, list):
        certification_labels = [canonical_family]

    metric_path = metrics_path_override or (
        context_root / "hepdata_dashi_native" / f"{metrics_family}_dashi_native_metrics.csv"
    )
    timeseries_path = (
        timeseries_path_override
        or pick_timeseries_root(context_root)
        or context_root / "hepdata_lyapunov_test_out" / "per_label_timeseries.csv"
    )

    measurement = load_family_measurement(context_root, canonical_family, family_spec)
    metrics = parse_metrics(metric_path, family_filters=[metrics_family])
    timeseries = parse_timeseries(timeseries_path, family_filters=[timeseries_family])
    certification = pick_certification(
        context_root,
        family=canonical_family,
        certification_labels=[str(label) for label in certification_labels],
        explicit=cert_path_override,
    )

    counts = {
        "measurement_rows": int(measurement.get("row_count", 0) or 0),
        "metric_rows": int(metrics.get("row_count", 0) or 0),
        "timeseries_rows": int(timeseries.get("row_count", 0) or 0),
        "has_certification": certification is not None,
    }
    statuses = {
        "measurement": str(measurement.get("status", "missing")),
        "metrics": str(metrics.get("status", "missing")),
        "timeseries": str(timeseries.get("status", "missing")),
        "certification": "ok" if certification is not None else "missing",
    }
    measurement_fields = measurement.get("field_status", {})
    measurement_fields_ready = (
        measurement_fields.get("x") == "ok"
        and measurement_fields.get("y") == "ok"
        and measurement_fields.get("cov") == "ok"
    )
    complete = (
        statuses["measurement"] == "ok"
        and statuses["metrics"] == "ok"
        and statuses["timeseries"] == "ok"
        and statuses["certification"] == "ok"
        and measurement_fields_ready
    )

    return {
        "family": family,
        "family_resolution": {
            "canonical_family": canonical_family,
            "resolution": family_spec.get("resolution", "implicit-exact"),
            "metrics_family": metrics_family,
            "timeseries_family": timeseries_family,
            "certification_labels": certification_labels,
        },
        "measurement": measurement,
        "metrics": metrics,
        "timeseries": timeseries,
        "certification": certification,
        "evidence_summary": {
            "counts": counts,
            "statuses": statuses,
            "measurement_fields": measurement_fields,
            "non_claim_boundary": (
                "Normalized empirical artifact only. "
                "No fitting, no live fetch, no theorem claim."
            ),
        },
        "validation_summary": {
            "counts": counts,
            "statuses": statuses,
            "measurement_fields": measurement_fields,
            "validation_status": (
                "empirical-artifact-ready"
                if complete
                else "partial-empirical-artifact"
            ),
            "non_claim_boundary": (
                "Validation here means packaging completeness only, "
                "not physics closure or theorem validation."
            ),
        },
    }


def build_payload(args: argparse.Namespace) -> dict[str, Any]:
    root = resolve_dashitest_root(Path(args.dashitest_root).resolve())
    root = resolve_data_root(root)
    crosswalk = load_family_crosswalk()
    family_filter = args.family

    metric_override = Path(args.metrics_path) if args.metrics_path else None
    timeseries_override = Path(args.timeseries_path) if args.timeseries_path else None
    cert_override = Path(args.certification_path) if args.certification_path else None

    family_names = infer_family_names(root, crosswalk)
    if family_filter:
        family_spec = resolve_family_spec(crosswalk, family_filter)
        canonical_family = str(family_spec.get("canonical_family", family_filter))
        if canonical_family not in family_names and family_filter not in family_names:
            raise SystemExit(
                f"family '{family_filter}' was not discovered under {root}; "
                "check --family or provide explicit --metrics-path and --timeseries-path"
            )
    else:
        family_spec = None

    payload: dict[str, Any] = {
        "artifact_schema": "dashi-hpdata-empirical-v1",
        "schema_version": "1.0.0",
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "source": {
            "dashitest_root": str(root),
            "input_root": str(Path(args.dashitest_root).resolve()),
            "input_family": family_filter,
            "family_crosswalk": {
                "path": str(FAMILY_CROSSWALK_PATH),
                "schema_version": crosswalk.get("schema_version", "missing"),
            },
        },
        "assumptions": {
            "input_filenames": {
                "measurement": [
                    "hepdata_npz(_all)/<family>.npz (preferred measurement surface)",
                    "hepdata_to_dashi/<family>/lenses_continuous.csv (fallback feature lens)",
                    "hepdata_to_dashi_<new|all>/<family>/lenses_continuous.csv",
                ],
                "metrics": [
                    "hepdata_dashi_native/<family>_dashi_native_metrics.csv",
                    "summary/flags rows filtered by label (if provided)",
                ],
                "timeseries": [
                    "hepdata_lyapunov_test_out(per family)/per_label_timeseries.csv",
                    "filter rows where label == family",
                ],
                "certification": [
                    "hepdata_lyapunov_test_out*/overall_certification.json",
                    "new/all/base variant chosen by family membership when available",
                ],
            },
            "scope": [
                "no fitting",
                "no HEPData fetch",
                "no cross-run recomputation",
                "schema-only normalization into JSON",
            ],
        },
    }

    if family_filter:
        payload["family"] = build_family_payload(
            root,
            canonical_family,
            family_spec or build_default_family_spec(canonical_family),
            metrics_path_override=metric_override,
            timeseries_path_override=timeseries_override,
            cert_path_override=cert_override,
        )
        return payload

    if not family_names:
        raise SystemExit(
            f"could not infer any family names from {root}. "
            "Pass --family or explicit files if you are not using canonical dashifine layout."
        )

    payload["family_count"] = len(family_names)
    payload["families"] = {
        family: build_family_payload(
            root,
            family,
            resolve_family_spec(crosswalk, family),
            metric_override,
            timeseries_override,
            cert_override,
        )
        for family in family_names
    }
    return payload


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Normalize legacy ../dashitest HEPData artifacts into one "
            "canonical JSON artifact consumable by dashi_agda."
        )
    )
    parser.add_argument(
        "dashitest_root",
        nargs="?",
        default="../dashitest",
        help="Path to dashitest root or any child folder containing dashifine outputs.",
    )
    parser.add_argument("--family", help="Restrict conversion to one family (e.g. pTll_50_76).")
    parser.add_argument("--metrics-path", help="Optional explicit metrics CSV (legacy compatibility).")
    parser.add_argument("--timeseries-path", help="Optional explicit per-label timeseries CSV.")
    parser.add_argument("--certification-path", help="Optional explicit overall certification JSON.")
    parser.add_argument(
        "--output",
        help="Write canonical JSON artifact to this path. If omitted, print to stdout.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    payload = build_payload(args)
    if args.output:
        path = Path(args.output)
        path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(str(path))
    else:
        print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
