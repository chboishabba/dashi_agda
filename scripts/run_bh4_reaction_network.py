#!/usr/bin/env python3
"""Run the bounded BH4 biochemical reaction-network audit.

Current executable slice: the exact QDPR/RHEA:32253 reaction.  The runner
recomputes atom and charge balance, emits a finite substrate->product graph and
records residuals.  It is not a kinetic, compartmental or disease model.
"""

from __future__ import annotations

import argparse
import csv
import json
import re
from collections import Counter
from pathlib import Path

FORMULA_TOKEN = re.compile(r"([A-Z][a-z]?)(\d*)")

QDPR = {
    "rhea_id": "RHEA:32253",
    "generic_rhea_id": "RHEA:17869",
    "enzyme": "QDPR/P09417",
    "participants": [
        {"side": "substrate", "chebi_id": "CHEBI:43120", "name": "(6R)-L-erythro-6,7-dihydrobiopterin", "formula": "C9H13N5O3", "charge": 0},
        {"side": "substrate", "chebi_id": "CHEBI:57945", "name": "NADH", "formula": "C21H27N7O14P2", "charge": -2},
        {"side": "substrate", "chebi_id": "CHEBI:15378", "name": "H+", "formula": "H", "charge": 1},
        {"side": "product", "chebi_id": "CHEBI:59560", "name": "(6R)-L-erythro-5,6,7,8-tetrahydrobiopterin", "formula": "C9H15N5O3", "charge": 0},
        {"side": "product", "chebi_id": "CHEBI:57540", "name": "NAD+", "formula": "C21H26N7O14P2", "charge": -1},
    ],
}


def parse_formula(formula: str) -> Counter[str]:
    parts = FORMULA_TOKEN.findall(formula)
    if not parts or "".join(el + count for el, count in parts) != formula:
        raise ValueError(f"unsupported molecular formula: {formula}")
    result: Counter[str] = Counter()
    for element, count in parts:
        result[element] += int(count or "1")
    return result


def side_totals(participants: list[dict], side: str) -> tuple[Counter[str], int]:
    atoms: Counter[str] = Counter()
    charge = 0
    for participant in participants:
        if participant["side"] != side:
            continue
        atoms.update(parse_formula(participant["formula"]))
        charge += int(participant["charge"])
    return atoms, charge


def audit_reaction(reaction: dict) -> dict:
    left_atoms, left_charge = side_totals(reaction["participants"], "substrate")
    right_atoms, right_charge = side_totals(reaction["participants"], "product")
    balanced = left_atoms == right_atoms and left_charge == right_charge
    substrates = [p["chebi_id"] for p in reaction["participants"] if p["side"] == "substrate"]
    products = [p["chebi_id"] for p in reaction["participants"] if p["side"] == "product"]
    edges = [
        {"from": source, "to": target, "reaction": reaction["rhea_id"]}
        for source in substrates
        for target in products
    ]
    return {
        "rhea_id": reaction["rhea_id"],
        "generic_rhea_id": reaction["generic_rhea_id"],
        "enzyme": reaction["enzyme"],
        "substrate_atoms": dict(sorted(left_atoms.items())),
        "product_atoms": dict(sorted(right_atoms.items())),
        "substrate_charge": left_charge,
        "product_charge": right_charge,
        "stoichiometrically_balanced": balanced,
        "participants": reaction["participants"],
        "graph_edges": edges,
        "kinetics_supplied": False,
        "compartment_state_supplied": False,
        "measured_flux_promoted": False,
        "disease_mechanism_promoted": False,
        "residuals": [
            "kinetic-law parameters not supplied",
            "compartment-specific BH4/BH2 amounts not supplied",
            "enzyme occupancy/activity not supplied",
            "transport and oxidation flux not supplied",
            "whole-system allocator balance not paid",
            "disease-level causal transition not paid",
        ],
    }


def write_outputs(result: dict, prefix: Path) -> None:
    prefix.parent.mkdir(parents=True, exist_ok=True)
    prefix.with_suffix(".json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    with prefix.with_suffix(".csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=["side", "chebi_id", "name", "formula", "charge"])
        writer.writeheader()
        writer.writerows(result["participants"])
    lines = [
        f"# BH4 reaction-network receipt: {result['rhea_id']}",
        "",
        f"- enzyme: {result['enzyme']}",
        f"- stoichiometrically balanced: `{str(result['stoichiometrically_balanced']).lower()}`",
        f"- substrate charge: {result['substrate_charge']}",
        f"- product charge: {result['product_charge']}",
        f"- kinetics supplied: `{str(result['kinetics_supplied']).lower()}`",
        f"- measured flux promoted: `{str(result['measured_flux_promoted']).lower()}`",
        f"- disease mechanism promoted: `{str(result['disease_mechanism_promoted']).lower()}`",
        "",
        "## Residuals",
        *[f"- {item}" for item in result["residuals"]],
    ]
    prefix.with_suffix(".md").write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--qdpr", action="store_true")
    parser.add_argument("--output-prefix", type=Path)
    args = parser.parse_args()
    if not args.qdpr:
        parser.error("select --qdpr for the current exact executable slice")
    result = audit_reaction(QDPR)
    if args.output_prefix:
        write_outputs(result, args.output_prefix)
    else:
        print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["stoichiometrically_balanced"] else 3


if __name__ == "__main__":
    raise SystemExit(main())
