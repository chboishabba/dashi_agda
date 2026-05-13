#!/usr/bin/env python3
"""Non-promoting W4/W5 public HEPData ratio-integral diagnostic.

The local CMS-SMP-20-003 CSVs in this lane expose one absolute Z-window
``d sigma / d phistar`` table (t21) plus ratio tables (t43/t45).  They do not
expose absolute ``d sigma / dM`` columns.  This runner therefore records that
``d sigma / dM`` mass-bin ratios are not computable from these CSV columns and
only computes the bounded ratio-table integral supported by the public data:

    sum_i Ratio_i * (d sigma_Z / d phistar)_i * Delta phistar_i
    ------------------------------------------------------------
    sum_i           (d sigma_Z / d phistar)_i * Delta phistar_i

This is diagnostic evidence only and does not promote W4 or W5.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any


DEFAULT_T21 = Path("scripts/data/hepdata/ins2079374_phistar_mass_76-106_t21.csv")
DEFAULT_T43 = Path("scripts/data/hepdata/ins2079374_phistar_mass_50-76_over_mass_76-106_t43.csv")
DEFAULT_T45 = Path("scripts/data/hepdata/ins2079374_phistar_mass_106-170_over_mass_76-106_t45.csv")

PHI = r"$\varphi^*$"
PHI_LOW = r"$\varphi^*$ LOW"
PHI_HIGH = r"$\varphi^*$ HIGH"
Z_DSIGMA_DPHI = r"$\mathrm{d}\sigma/\mathrm{d}\varphi^*$ [pb]"

CHECKED_PUBLIC_LINKS = [
    {
        "url": "https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/",
        "access": "HTTP 200 via public CMS results page",
        "finding": (
            "Describes corrected differential cross sections and ratios in mass windows; "
            "does not publish A(M, phi*) or a phi-star-to-mass conversion law."
        ),
    },
    {
        "url": (
            "https://cms-results.web.cern.ch/cms-results/public-results/publications/"
            "SMP-20-003/SMP-20-003_hepdata/submission.yaml"
        ),
        "access": "HTTP 200",
        "finding": (
            "Lists phistar measurements, covariance matrices, and response matrices; "
            "no acceptance/efficiency central-value surface is listed."
        ),
    },
    {
        "url": "https://www.hepdata.net/record/ins2079374?format=json",
        "access": "HTTP 200",
        "finding": (
            "Metadata enumerates phistar cross-section, ratio, covariance, and response "
            "tables t19/t21/t23, t43/t45, t20/t22/t44/t46, and t68-t73."
        ),
    },
    {
        "url": (
            "https://cms-results.web.cern.ch/cms-results/public-results/publications/"
            "SMP-20-003/SMP-20-003_hepdata/electron_response_phistar_mass_50-76.yaml"
        ),
        "access": "HTTP 200",
        "finding": (
            "Response YAML has dependent variable P for detector-bin migration; it is not "
            "an acceptance/efficiency surface A(M, phi*)."
        ),
    },
    {
        "url": "https://zenodo.org/record/4946277",
        "access": "HTTP 200 via Zenodo API",
        "finding": (
            "Additional resource points to a hepdata_lib package artifact, not a CMS "
            "acceptance/efficiency or conversion-law payload."
        ),
    },
]

URL_FAILURES = [
    {
        "url": "https://www.hepdata.net/record/ins2079374?format=json&table=Table%2043",
        "redirected_to": "https://www.hepdata.net/download/table/ins2079374/Table%2043/1/json",
        "status": "HTTP 403 / Cloudflare challenge from CLI",
        "manual_action": (
            "Browser/manual download is only needed for canonical table JSON payloads; "
            "it would not supply the missing A(M, phi*) field."
        ),
    }
]

EXACT_MISSING_PUBLIC_FIELD = (
    "central-value acceptance/efficiency surface A(M, phi*) for the CMS-SMP-20-003 "
    "mass windows 50-76, 76-106, and 106-170 GeV, or an accepted observable-conversion "
    "law from DSIG/DPHISTAR ratio-table integrals to mass-integrated cross-section/PDF "
    "correction ratios"
)


@dataclass(frozen=True)
class CsvTable:
    path: Path
    metadata: dict[str, str]
    header: list[str]
    rows: list[dict[str, str]]


def _parse_metadata(line: str) -> tuple[str, str] | None:
    if not line.startswith("#:"):
        return None
    key_value = line[2:].strip()
    if ":" not in key_value:
        return None
    key, value = key_value.split(":", 1)
    return key.strip(), value.strip()


def read_hepdata_csv(path: Path) -> CsvTable:
    metadata: dict[str, str] = {}
    header: list[str] | None = None
    rows: list[dict[str, str]] = []

    with path.open(newline="", encoding="utf-8") as handle:
        for raw_line in handle:
            parsed = _parse_metadata(raw_line)
            if parsed is not None:
                key, value = parsed
                metadata[key] = value
                continue
            if raw_line.startswith("#") or not raw_line.strip():
                continue
            header = next(csv.reader([raw_line]))
            break

        if header is None:
            raise ValueError(f"{path}: missing CSV header")

        for row in csv.DictReader(handle, fieldnames=header):
            if row and any(value not in (None, "") for value in row.values()):
                rows.append(row)

    if not rows:
        raise ValueError(f"{path}: no data rows")
    return CsvTable(path=path, metadata=metadata, header=header, rows=rows)


def finite_float(row: dict[str, str], column: str, path: Path) -> float:
    if column not in row:
        raise ValueError(f"{path}: missing required column {column!r}")
    try:
        value = float(row[column])
    except (TypeError, ValueError) as exc:
        raise ValueError(f"{path}: column {column!r} is not numeric: {row[column]!r}") from exc
    if not math.isfinite(value):
        raise ValueError(f"{path}: column {column!r} is not finite: {row[column]!r}")
    return value


def table_kind(table: CsvTable) -> dict[str, Any]:
    observable = table.metadata.get("keyword observables", "")
    description = table.metadata.get("description", "")
    has_ratio = "Ratio" in table.header
    has_absolute_dsigma_dphi = Z_DSIGMA_DPHI in table.header
    has_dsigma_dm = any("d}M" in column or "/\\mathrm{d}M" in column for column in table.header)
    is_ratio_table = has_ratio or observable == "DSIG/DPHISTAR / DSIG/DPHISTAR"
    return {
        "path": str(table.path),
        "table_doi": table.metadata.get("table_doi"),
        "name": table.metadata.get("name"),
        "observable": observable,
        "description": description,
        "row_count": len(table.rows),
        "has_ratio_column": has_ratio,
        "has_absolute_dsigma_dphistar_column": has_absolute_dsigma_dphi,
        "has_dsigma_dM_column": has_dsigma_dm,
        "is_ratio_table": is_ratio_table,
        "values_normalized_by_bin_width": "not normalized by the bin width" not in description,
    }


def require_matching_phi_bins(z_table: CsvTable, ratio_table: CsvTable) -> None:
    if len(z_table.rows) != len(ratio_table.rows):
        raise ValueError(
            f"{ratio_table.path}: row count {len(ratio_table.rows)} does not match "
            f"{z_table.path}: {len(z_table.rows)}"
        )

    for index, (z_row, ratio_row) in enumerate(zip(z_table.rows, ratio_table.rows), start=1):
        z_low = finite_float(z_row, PHI_LOW, z_table.path)
        z_high = finite_float(z_row, PHI_HIGH, z_table.path)
        ratio_low = finite_float(ratio_row, PHI_LOW, ratio_table.path)
        ratio_high = finite_float(ratio_row, PHI_HIGH, ratio_table.path)
        if abs(z_low - ratio_low) > 1.0e-12 or abs(z_high - ratio_high) > 1.0e-12:
            raise ValueError(
                f"{ratio_table.path}: phi bin {index} does not match denominator "
                f"({ratio_low}, {ratio_high}) != ({z_low}, {z_high})"
            )


def integrated_ratio(z_table: CsvTable, ratio_table: CsvTable) -> dict[str, Any]:
    require_matching_phi_bins(z_table, ratio_table)

    denominator_pb = 0.0
    numerator_pb = 0.0
    ratio_sum = 0.0
    ratio_min = math.inf
    ratio_max = -math.inf

    for z_row, ratio_row in zip(z_table.rows, ratio_table.rows):
        width = finite_float(z_row, PHI_HIGH, z_table.path) - finite_float(z_row, PHI_LOW, z_table.path)
        if width <= 0.0:
            raise ValueError(f"{z_table.path}: non-positive phi bin width {width}")
        z_dsigma_dphi = finite_float(z_row, Z_DSIGMA_DPHI, z_table.path)
        ratio = finite_float(ratio_row, "Ratio", ratio_table.path)
        if z_dsigma_dphi < 0.0 or ratio < 0.0:
            raise ValueError(f"{ratio_table.path}: negative cross-section input")

        denominator_pb += z_dsigma_dphi * width
        numerator_pb += ratio * z_dsigma_dphi * width
        ratio_sum += ratio
        ratio_min = min(ratio_min, ratio)
        ratio_max = max(ratio_max, ratio)

    if denominator_pb <= 0.0:
        raise ValueError(f"{z_table.path}: denominator integral is not positive")

    return {
        "ratio_table": str(ratio_table.path),
        "ratio_table_doi": ratio_table.metadata.get("table_doi"),
        "ratio_name": ratio_table.metadata.get("name"),
        "formula": "sum Ratio_i * (dsigma_Z/dphistar)_i * dphistar_i / sum (dsigma_Z/dphistar)_i * dphistar_i",
        "phi_bin_count": len(ratio_table.rows),
        "phi_range": [
            finite_float(z_table.rows[0], PHI_LOW, z_table.path),
            finite_float(z_table.rows[-1], PHI_HIGH, z_table.path),
        ],
        "z_denominator_integral_pb": denominator_pb,
        "implied_numerator_integral_pb": numerator_pb,
        "integrated_ratio_over_z": numerator_pb / denominator_pb,
        "unweighted_ratio_mean": ratio_sum / len(ratio_table.rows),
        "ratio_min": ratio_min,
        "ratio_max": ratio_max,
    }


def build_payload(t21: Path, t43: Path, t45: Path) -> dict[str, Any]:
    z_table = read_hepdata_csv(t21)
    ratio_tables = [read_hepdata_csv(t43), read_hepdata_csv(t45)]
    table_kinds = [table_kind(z_table), *(table_kind(table) for table in ratio_tables)]

    unsupported_reasons = []
    if not any(kind["has_dsigma_dM_column"] for kind in table_kinds):
        unsupported_reasons.append("none of t21/t43/t45 exposes a dsigma/dM column")
    if any(kind["is_ratio_table"] for kind in table_kinds[1:]):
        unsupported_reasons.append("t43 and t45 expose Ratio columns for DSIG/DPHISTAR / DSIG/DPHISTAR")
    if not table_kinds[0]["has_absolute_dsigma_dphistar_column"]:
        unsupported_reasons.append("t21 does not expose the required Z-window dsigma/dphistar denominator")

    computed = {
        "t43_50_76_over_76_106": integrated_ratio(z_table, ratio_tables[0]),
        "t45_106_170_over_76_106": integrated_ratio(z_table, ratio_tables[1]),
    }
    computed["t45_over_t43_from_public_ratio_integrals"] = (
        computed["t45_106_170_over_76_106"]["implied_numerator_integral_pb"]
        / computed["t43_50_76_over_76_106"]["implied_numerator_integral_pb"]
    )

    return {
        "artifact_schema": "dashi-w4w5-hepdata-public-ratio-integral-diagnostic-v1",
        "status": "non_promoting_public_hepdata_ratio_integral_diagnostic",
        "requested_target": "bin-integrated dsigma/dM ratios from public HEPData tables",
        "target_computable_from_columns": False,
        "unsupported_target_reasons": unsupported_reasons,
        "supported_computation": (
            "phistar-bin integrated DSIG/DPHISTAR ratio-table integral using t21 as the "
            "public Z-window denominator"
        ),
        "checked_public_links": CHECKED_PUBLIC_LINKS,
        "url_failures": URL_FAILURES,
        "exact_missing_public_field": EXACT_MISSING_PUBLIC_FIELD,
        "tables": table_kinds,
        "computed_ratios": computed,
        "governance": {
            "no_w4_promotion": True,
            "no_w5_promotion": True,
            "no_authority_promotion": True,
            "does_not_construct_accepted_dy_luminosity_convention": True,
            "does_not_claim_dsigma_dM_from_ratio_tables": True,
        },
    }


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--t21", type=Path, default=DEFAULT_T21)
    parser.add_argument("--t43", type=Path, default=DEFAULT_T43)
    parser.add_argument("--t45", type=Path, default=DEFAULT_T45)
    parser.add_argument("--output", type=Path)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        payload = build_payload(args.t21, args.t43, args.t45)
    except (OSError, ValueError) as exc:
        print(f"hepdata ratio-integral diagnostic failed: {exc}", file=sys.stderr)
        return 2

    encoded = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded, encoding="utf-8")
    print(encoded, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
