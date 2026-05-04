#!/usr/bin/env python3
"""Diagnose local HEPData ratio-table conventions for T43/T45 CSV exports."""

from __future__ import annotations

import argparse
import csv
from dataclasses import dataclass
from pathlib import Path
from statistics import mean


DEFAULT_CSVS = (
    Path("scripts/data/hepdata/ins2079374_phistar_mass_50-76_over_mass_76-106_t43.csv"),
    Path("scripts/data/hepdata/ins2079374_phistar_mass_106-170_over_mass_76-106_t45.csv"),
)


@dataclass(frozen=True)
class RatioTable:
    path: Path
    metadata: dict[str, str]
    header: list[str]
    ratios: list[float]


def _parse_metadata(line: str) -> tuple[str, str] | None:
    if not line.startswith("#:"):
        return None
    key_value = line[2:].strip()
    if ":" not in key_value:
        return None
    key, value = key_value.split(":", 1)
    return key.strip(), value.strip()


def read_ratio_table(path: Path) -> RatioTable:
    metadata: dict[str, str] = {}
    header: list[str] | None = None
    rows: list[list[str]] = []

    with path.open(newline="", encoding="utf-8") as handle:
        for raw_line in handle:
            parsed = _parse_metadata(raw_line)
            if parsed is not None:
                key, value = parsed
                metadata[key] = value
                continue
            if raw_line.startswith("#"):
                continue
            if raw_line.strip():
                header = next(csv.reader([raw_line]))
                break

        if header is None:
            raise ValueError(f"{path}: missing CSV header")

        rows.extend(csv.reader(handle))

    if "Ratio" not in header:
        raise ValueError(f"{path}: missing required 'Ratio' column in {header!r}")

    ratio_index = header.index("Ratio")
    ratios = [float(row[ratio_index]) for row in rows if row]
    if not ratios:
        raise ValueError(f"{path}: no ratio data rows")

    return RatioTable(path=path, metadata=metadata, header=header, ratios=ratios)


def convention_evidence(table: RatioTable) -> list[str]:
    description = table.metadata.get("description", "")
    observable = table.metadata.get("keyword observables", "")
    evidence: list[str] = []

    if "measured differential cross section" in description:
        evidence.append("description uses measured differential cross section")
    if "divided by the measured differential cross section" in description:
        evidence.append("description defines a differential cross-section ratio")
    if "not normalized by the bin width" in description:
        evidence.append("description explicitly says values are not normalized by bin width")
    if observable == "DSIG/DPHISTAR / DSIG/DPHISTAR":
        evidence.append("observable is DSIG/DPHISTAR / DSIG/DPHISTAR")
    return evidence


def print_table_report(table: RatioTable) -> None:
    ratios = table.ratios
    print(f"file: {table.path}")
    print(f"table_doi: {table.metadata.get('table_doi', '<missing>')}")
    print(f"name: {table.metadata.get('name', '<missing>')}")
    print(f"description: {table.metadata.get('description', '<missing>')}")
    print(f"observable: {table.metadata.get('keyword observables', '<missing>')}")
    print(f"rows: {len(ratios)}")
    print(f"data_min: {min(ratios):.6g}")
    print(f"data_max: {max(ratios):.6g}")
    print(f"data_mean: {mean(ratios):.6g}")
    print("evidence:")
    for item in convention_evidence(table):
        print(f"  - {item}")
    print()


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Diagnose whether local HEPData ratio CSVs are total-normalized or differential cross-section ratios."
    )
    parser.add_argument(
        "csv",
        nargs="*",
        type=Path,
        default=DEFAULT_CSVS,
        help="HEPData ratio CSV files to inspect.",
    )
    args = parser.parse_args()

    tables = [read_ratio_table(path) for path in args.csv]
    for table in tables:
        print_table_report(table)

    all_have_dsig_ratio = all(
        table.metadata.get("keyword observables") == "DSIG/DPHISTAR / DSIG/DPHISTAR"
        for table in tables
    )
    all_describe_differential_ratio = all(
        "measured differential cross section" in table.metadata.get("description", "")
        and "divided by the measured differential cross section" in table.metadata.get("description", "")
        for table in tables
    )

    print("conclusion:")
    if all_have_dsig_ratio and all_describe_differential_ratio:
        print(
            "  Both inspected tables are unnormalized differential cross-section ratios "
            "(DSIG/DPHISTAR divided by DSIG/DPHISTAR), not total-normalized differential ratios."
        )
    else:
        print("  Convention evidence is incomplete; inspect metadata before using these tables.")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
