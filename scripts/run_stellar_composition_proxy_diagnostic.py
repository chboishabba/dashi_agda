#!/usr/bin/env python3
"""Receipt-gated stellar-composition proxy diagnostic.

This script emits a deterministic composition -> proxy-observable receipt for
the staged stellar simulator lane.  It is a bounded proxy only: it does not
promote carrier-internal stellar physics, stellar evolution, or solar
instability claims.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any


DEFAULT_JSON_OUTPUT = Path("scripts/data/outputs/stellar_composition_proxy_diagnostic.json")
DEFAULT_CSV_OUTPUT = Path("scripts/data/outputs/stellar_composition_proxy_diagnostic.csv")
DEFAULT_MD_OUTPUT = Path("scripts/data/outputs/stellar_composition_proxy_diagnostic.md")

PROMOTION_STATUS = "NO_PROMOTION"
TOTAL_TOLERANCE = 1.0e-6
OUTPUT_STEM = "stellar_composition_proxy_diagnostic"
FAIL_CLOSED_FLAGS = {
    "carrier_internal_prediction": False,
    "stellar_evolution_promoted": False,
    "solar_instability_claim_promoted": False,
    "external_baseline_or_proxy_only": True,
}
PROMOTION_BLOCKERS = [
    "missing_carrier_derived_matter_force_law",
    "missing_eos_authority",
    "missing_opacity_authority",
    "missing_reaction_network_authority",
    "missing_hydrostatic_solver_authority",
    "missing_empirical_validation_receipt",
]

REFERENCE_LABEL = "solar_reference"
REFERENCE_X = 0.7381
REFERENCE_Y = 0.2485
REFERENCE_Z = 0.0134
HYDROGEN_PERTURBATION = 0.03


@dataclass(frozen=True)
class CompositionCase:
    label: str
    x_hydrogen: float
    y_helium: float
    z_metals: float
    input_total: float
    normalized: bool
    input_x_hydrogen: float
    input_y_helium: float
    input_z_metals: float


@dataclass(frozen=True)
class ProxyRecord:
    label: str
    x_hydrogen: float
    y_helium: float
    z_metals: float
    input_total: float
    normalized: bool
    mean_molecular_weight_proxy_mu: float
    support_proxy_ratio_vs_reference: float
    energy_generation_proxy_ratio_vs_reference: float
    stability_regime_label: str

    def as_row(self) -> dict[str, Any]:
        return {
            "label": self.label,
            "x_hydrogen": self.x_hydrogen,
            "y_helium": self.y_helium,
            "z_metals": self.z_metals,
            "input_total": self.input_total,
            "normalized": self.normalized,
            "mean_molecular_weight_proxy_mu": self.mean_molecular_weight_proxy_mu,
            "support_proxy_ratio_vs_reference": self.support_proxy_ratio_vs_reference,
            "energy_generation_proxy_ratio_vs_reference": (
                self.energy_generation_proxy_ratio_vs_reference
            ),
            "stability_regime_label": self.stability_regime_label,
            "carrier_internal_prediction": False,
            "stellar_evolution_promoted": False,
            "solar_instability_claim_promoted": False,
            "external_baseline_or_proxy_only": True,
            "promotion_status": PROMOTION_STATUS,
        }


def finite_nonnegative(value: float, name: str, label: str) -> float:
    if not math.isfinite(value):
        raise ValueError(f"composition {label!r} has non-finite {name}")
    if value < 0.0:
        raise ValueError(f"composition {label!r} has negative {name}")
    return value


def normalize_label(label: str) -> str:
    stripped = label.strip()
    if not stripped:
        raise ValueError("composition label must not be empty")
    if "," in stripped or "\n" in stripped or "\r" in stripped:
        raise ValueError(f"composition label {label!r} must not contain commas or newlines")
    return stripped


def build_case(label: str, x: float, y: float, z: float, *, normalize: bool) -> CompositionCase:
    clean_label = normalize_label(label)
    x = finite_nonnegative(x, "X", clean_label)
    y = finite_nonnegative(y, "Y", clean_label)
    z = finite_nonnegative(z, "Z", clean_label)
    total = x + y + z
    if not math.isfinite(total):
        raise ValueError(f"composition {clean_label!r} has non-finite total")
    if total <= 0.0:
        raise ValueError(f"composition {clean_label!r} total must be positive")

    if normalize:
        return CompositionCase(
            label=clean_label,
            x_hydrogen=x / total,
            y_helium=y / total,
            z_metals=z / total,
            input_total=total,
            normalized=True,
            input_x_hydrogen=x,
            input_y_helium=y,
            input_z_metals=z,
        )

    if abs(total - 1.0) > TOTAL_TOLERANCE:
        raise ValueError(
            f"composition {clean_label!r} total is {total:.12g}; "
            f"expected 1 +/- {TOTAL_TOLERANCE:g} unless --normalize is set"
        )
    return CompositionCase(
        label=clean_label,
        x_hydrogen=x,
        y_helium=y,
        z_metals=z,
        input_total=total,
        normalized=False,
        input_x_hydrogen=x,
        input_y_helium=y,
        input_z_metals=z,
    )


def default_cases(*, normalize: bool) -> list[CompositionCase]:
    return [
        build_case(REFERENCE_LABEL, REFERENCE_X, REFERENCE_Y, REFERENCE_Z, normalize=normalize),
        build_case(
            "hydrogen_minus_0.03",
            REFERENCE_X - HYDROGEN_PERTURBATION,
            REFERENCE_Y + HYDROGEN_PERTURBATION,
            REFERENCE_Z,
            normalize=normalize,
        ),
        build_case(
            "hydrogen_plus_0.03",
            REFERENCE_X + HYDROGEN_PERTURBATION,
            REFERENCE_Y - HYDROGEN_PERTURBATION,
            REFERENCE_Z,
            normalize=normalize,
        ),
    ]


def mean_molecular_weight_proxy(case: CompositionCase) -> float:
    denominator = (
        2.0 * case.x_hydrogen
        + 0.75 * case.y_helium
        + 0.5 * case.z_metals
    )
    if denominator <= 0.0:
        raise ValueError(f"composition {case.label!r} has zero ionized-particle denominator")
    return 1.0 / denominator


def energy_generation_proxy(case: CompositionCase, mu: float) -> float:
    return case.x_hydrogen * case.x_hydrogen * mu**4


def stability_regime_label(support_ratio: float, energy_ratio: float) -> str:
    if 0.95 <= support_ratio <= 1.05 and 0.85 <= energy_ratio <= 1.15:
        return "reference_like_bounded_proxy"
    if support_ratio < 0.95 and energy_ratio < 0.85:
        return "hydrogen_depleted_lower_support_lower_energy_proxy"
    if support_ratio > 1.05 and energy_ratio > 1.15:
        return "hydrogen_enriched_higher_support_higher_energy_proxy"
    if energy_ratio < 0.85:
        return "lower_energy_proxy"
    if energy_ratio > 1.15:
        return "higher_energy_proxy"
    if support_ratio < 0.95:
        return "lower_support_proxy"
    if support_ratio > 1.05:
        return "higher_support_proxy"
    return "mixed_bounded_proxy"


def build_records(cases: list[CompositionCase]) -> list[dict[str, Any]]:
    reference_case = next((case for case in cases if case.label == REFERENCE_LABEL), cases[0])
    reference_mu = mean_molecular_weight_proxy(reference_case)
    reference_support = 1.0 / reference_mu
    reference_energy = energy_generation_proxy(reference_case, reference_mu)

    records: list[dict[str, Any]] = []
    for case in cases:
        mu = mean_molecular_weight_proxy(case)
        support = 1.0 / mu
        energy = energy_generation_proxy(case, mu)
        support_ratio = support / reference_support
        energy_ratio = energy / reference_energy
        stability_label = stability_regime_label(support_ratio, energy_ratio)
        stability_score = 1.0 / (
            1.0 + abs(support_ratio - 1.0) + abs(energy_ratio - 1.0)
        )
        record = ProxyRecord(
            label=case.label,
            x_hydrogen=case.x_hydrogen,
            y_helium=case.y_helium,
            z_metals=case.z_metals,
            input_total=case.input_total,
            normalized=case.normalized,
            mean_molecular_weight_proxy_mu=mu,
            support_proxy_ratio_vs_reference=support_ratio,
            energy_generation_proxy_ratio_vs_reference=energy_ratio,
            stability_regime_label=stability_label,
        )
        row = record.as_row()
        row.update(
            {
                "hydrogen_mass_fraction": case.x_hydrogen,
                "helium_mass_fraction": case.y_helium,
                "metal_mass_fraction": case.z_metals,
                "total_mass_fraction": (
                    case.x_hydrogen + case.y_helium + case.z_metals
                ),
                "mean_molecular_weight_proxy": mu,
                "support_proxy_ratio": support_ratio,
                "energy_generation_proxy_ratio": energy_ratio,
                "stability_score": stability_score,
                "regime_label": stability_label,
                "input_composition": {
                    "X": case.input_x_hydrogen,
                    "Y": case.input_y_helium,
                    "Z": case.input_z_metals,
                },
                "composition": {
                    "X": case.x_hydrogen,
                    "Y": case.y_helium,
                    "Z": case.z_metals,
                },
                "composition_normalized": case.normalized,
                "baseline_normalized": case.label == REFERENCE_LABEL,
                "claim_boundary": dict(FAIL_CLOSED_FLAGS),
                "solar_instability_claim": False,
                "stability_observable": {
                    "claim": "no_solar_instability_claim",
                    "promoted": False,
                    "score": stability_score,
                    "regime_label": stability_label,
                },
            }
        )
        records.append(row)
    return records


def build_payload(
    records: list[dict[str, Any]],
    *,
    normalize: bool,
    output_paths: dict[str, str],
) -> dict[str, Any]:
    return {
        "diagnostic": OUTPUT_STEM,
        "artifact_schema": "dashi-stellar-composition-proxy-diagnostic-v1",
        "promotion_status": PROMOTION_STATUS,
        **FAIL_CLOSED_FLAGS,
        "status": "proxy_only_no_promotion",
        "output_paths": output_paths,
        "fail_closed_flags": dict(FAIL_CLOSED_FLAGS),
        "normalization_applied": normalize,
        "composition_total_tolerance": TOTAL_TOLERANCE,
        "reference_case": REFERENCE_LABEL,
        "formulas": {
            "mean_molecular_weight_proxy_mu": "1/(2X + 0.75Y + 0.5Z)",
            "support_proxy": "1/mu at fixed density and temperature",
            "support_proxy_ratio_vs_reference": "support_proxy/support_proxy(solar_reference)",
            "energy_generation_proxy": "X^2 * mu^4",
            "energy_generation_proxy_ratio_vs_reference": (
                "energy_generation_proxy/energy_generation_proxy(solar_reference)"
            ),
        },
        "scope": [
            "composition mass-fraction proxy",
            "fully ionized mean molecular weight proxy",
            "bounded support and energy-generation proxy ratios",
            "fail-closed promotion receipt",
        ],
        "non_promotion_reason": (
            "The diagnostic uses deterministic proxy equations and does not supply "
            "carrier-derived matter/force law, EOS, opacity, nuclear reaction network, "
            "hydrostatic solver, or empirical stellar-model validation receipts."
        ),
        "models_not_supplied": PROMOTION_BLOCKERS,
        "promotion": {
            "state": "blocked",
            "flags": dict(FAIL_CLOSED_FLAGS),
            "blockers": PROMOTION_BLOCKERS,
        },
        "rows": records,
        "records": records,
    }


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, records: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fieldnames = [
        "label",
        "x_hydrogen",
        "y_helium",
        "z_metals",
        "input_total",
        "normalized",
        "mean_molecular_weight_proxy_mu",
        "support_proxy_ratio_vs_reference",
        "energy_generation_proxy_ratio_vs_reference",
        "stability_regime_label",
        "carrier_internal_prediction",
        "stellar_evolution_promoted",
        "solar_instability_claim_promoted",
        "external_baseline_or_proxy_only",
        "promotion_status",
        "hydrogen_mass_fraction",
        "helium_mass_fraction",
        "metal_mass_fraction",
        "total_mass_fraction",
        "mean_molecular_weight_proxy",
        "support_proxy_ratio",
        "energy_generation_proxy_ratio",
        "stability_score",
        "regime_label",
        "solar_instability_claim",
    ]
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for record in records:
            writer.writerow(
                {
                    key: str(value).lower() if isinstance(value, bool) else value
                    for key, value in record.items()
                    if key in fieldnames
                }
            )


def format_float(value: Any) -> str:
    if isinstance(value, float):
        return f"{value:.12g}"
    return str(value)


def write_markdown(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    lines = [
        "# Stellar Composition Proxy Diagnostic",
        "",
        f"- diagnostic: `{payload['diagnostic']}`",
        f"- artifact_schema: `{payload['artifact_schema']}`",
        f"- status: `{payload['status']}`",
        f"- promotion_status: `{payload['promotion_status']}`",
        f"- carrier_internal_prediction: `{str(payload['carrier_internal_prediction']).lower()}`",
        f"- stellar_evolution_promoted: `{str(payload['stellar_evolution_promoted']).lower()}`",
        f"- solar_instability_claim_promoted: `{str(payload['solar_instability_claim_promoted']).lower()}`",
        f"- external_baseline_or_proxy_only: `{str(payload['external_baseline_or_proxy_only']).lower()}`",
        "",
        "## Proxy Formulas",
        "",
    ]
    for name, formula in payload["formulas"].items():
        lines.append(f"- `{name}`: `{formula}`")
    lines.extend(
        [
            "",
            "## Records",
            "",
            "| label | X | Y | Z | mu | support ratio | energy ratio | regime |",
            "| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |",
        ]
    )
    for record in payload["records"]:
        lines.append(
            "| {label} | {x} | {y} | {z} | {mu} | {support} | {energy} | {regime} |".format(
                label=record["label"],
                x=format_float(record["x_hydrogen"]),
                y=format_float(record["y_helium"]),
                z=format_float(record["z_metals"]),
                mu=format_float(record["mean_molecular_weight_proxy_mu"]),
                support=format_float(record["support_proxy_ratio_vs_reference"]),
                energy=format_float(record["energy_generation_proxy_ratio_vs_reference"]),
                regime=record["stability_regime_label"],
            )
        )
    lines.extend(["", "## Non-Promotion Reason", "", str(payload["non_promotion_reason"]), ""])
    path.write_text("\n".join(lines), encoding="utf-8")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Emit a non-promoting stellar-composition proxy diagnostic."
    )
    parser.add_argument("--json-output", type=Path, default=DEFAULT_JSON_OUTPUT)
    parser.add_argument("--csv-output", type=Path, default=DEFAULT_CSV_OUTPUT)
    parser.add_argument("--md-output", type=Path, default=DEFAULT_MD_OUTPUT)
    parser.add_argument(
        "--markdown-output",
        type=Path,
        help="Alias for --md-output.",
    )
    parser.add_argument(
        "--out-dir",
        type=Path,
        help="Write standard JSON/CSV/Markdown outputs into this directory.",
    )
    parser.add_argument(
        "--composition",
        nargs=4,
        action="append",
        metavar=("LABEL", "X", "Y", "Z"),
        default=[],
        help="Add a composition case with mass fractions X, Y, Z. May be repeated.",
    )
    parser.add_argument(
        "--normalize",
        action="store_true",
        help="Normalize composition totals to one instead of rejecting totals outside tolerance.",
    )
    return parser.parse_args()


def parse_composition_arg(raw: list[str], *, normalize: bool) -> CompositionCase:
    label, x_raw, y_raw, z_raw = raw
    try:
        x = float(x_raw)
        y = float(y_raw)
        z = float(z_raw)
    except ValueError as exc:
        raise ValueError(f"composition {label!r} has a non-numeric mass fraction") from exc
    return build_case(label, x, y, z, normalize=normalize)


def main() -> int:
    args = parse_args()
    if args.out_dir is not None:
        args.json_output = args.out_dir / f"{OUTPUT_STEM}.json"
        args.csv_output = args.out_dir / f"{OUTPUT_STEM}.csv"
        args.md_output = args.out_dir / f"{OUTPUT_STEM}.md"
    if args.markdown_output is not None:
        args.md_output = args.markdown_output

    try:
        cases = default_cases(normalize=args.normalize)
        cases.extend(
            parse_composition_arg(raw, normalize=args.normalize)
            for raw in args.composition
        )
        records = build_records(cases)
        output_paths = {
            "json": str(args.json_output),
            "csv": str(args.csv_output),
            "markdown": str(args.md_output),
        }
        payload = build_payload(
            records,
            normalize=args.normalize,
            output_paths=output_paths,
        )
    except ValueError as exc:
        raise SystemExit(str(exc)) from exc

    write_json(args.json_output, payload)
    write_csv(args.csv_output, records)
    write_markdown(args.md_output, payload)
    print(json.dumps(payload, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
