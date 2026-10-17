#!/usr/bin/env python3
"""Run the bounded BH4 biochemical reaction-network audit.

Modes:
  --qdpr
      audit the exact QDPR/RHEA:32253 fixture.
  --certificate PATH
      consume a Rhea/ChEBI panel certificate produced by
      acquire_rhea_chebi_bh4_reactions.py and audit every reaction whose
      participant coefficient/formula/charge data are finite and parseable.

The runner recomputes atom and charge balance and emits a finite graph. It is
not a kinetic, compartmental, allocator or disease model.
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
        {"side": "substrate", "coefficient": 1, "chebi_id": "CHEBI:43120", "name": "(6R)-L-erythro-6,7-dihydrobiopterin", "formula": "C9H13N5O3", "charge": 0},
        {"side": "substrate", "coefficient": 1, "chebi_id": "CHEBI:57945", "name": "NADH", "formula": "C21H27N7O14P2", "charge": -2},
        {"side": "substrate", "coefficient": 1, "chebi_id": "CHEBI:15378", "name": "H+", "formula": "H", "charge": 1},
        {"side": "product", "coefficient": 1, "chebi_id": "CHEBI:59560", "name": "(6R)-L-erythro-5,6,7,8-tetrahydrobiopterin", "formula": "C9H15N5O3", "charge": 0},
        {"side": "product", "coefficient": 1, "chebi_id": "CHEBI:57540", "name": "NAD+", "formula": "C21H26N7O14P2", "charge": -1},
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


def _integer(value: object, label: str) -> int:
    text = str(value)
    if not re.fullmatch(r"[+-]?\d+", text):
        raise ValueError(f"non-integer {label}: {text}")
    return int(text)


def side_totals(participants: list[dict], side: str) -> tuple[Counter[str], int]:
    atoms: Counter[str] = Counter()
    charge = 0
    for participant in participants:
        if participant["side"] != side:
            continue
        coefficient = _integer(participant.get("coefficient", 1), "coefficient")
        if coefficient < 0:
            raise ValueError(f"negative coefficient: {coefficient}")
        formula_atoms = parse_formula(str(participant["formula"]))
        for element, count in formula_atoms.items():
            atoms[element] += coefficient * count
        charge += coefficient * _integer(participant["charge"], "charge")
    return atoms, charge


def audit_reaction(reaction: dict) -> dict:
    left_atoms, left_charge = side_totals(reaction["participants"], "substrate")
    right_atoms, right_charge = side_totals(reaction["participants"], "product")
    balanced = left_atoms == right_atoms and left_charge == right_charge
    substrates = [p.get("chebi_id") or p.get("compound_uri") for p in reaction["participants"] if p["side"] == "substrate"]
    products = [p.get("chebi_id") or p.get("compound_uri") for p in reaction["participants"] if p["side"] == "product"]
    edges = [
        {"from": source, "to": target, "reaction": reaction["rhea_id"]}
        for source in substrates
        for target in products
    ]
    return {
        "rhea_id": reaction["rhea_id"],
        "generic_rhea_id": reaction.get("generic_rhea_id"),
        "enzyme": reaction.get("enzyme"),
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


def audit_certificate(path: Path) -> dict:
    certificate = json.loads(path.read_text(encoding="utf-8"))
    audited: list[dict] = []
    residual: list[dict] = []
    for reaction in certificate.get("reactions", []):
        rid = reaction.get("rhea_id", "unidentified")
        if not reaction.get("formula_charge_ready"):
            residual.append({"rhea_id": rid, "reason": "participant formula/charge/coefficient receipt incomplete"})
            continue
        try:
            audited.append(audit_reaction({"rhea_id": rid, "participants": reaction.get("participants", [])}))
        except (KeyError, TypeError, ValueError) as exc:
            residual.append({"rhea_id": rid, "reason": str(exc)})
    balanced = sum(bool(row["stoichiometrically_balanced"]) for row in audited)
    return {
        "schema": "dashi.bh4-reaction-network-audit.v2",
        "source_certificate": str(path),
        "reaction_identity_rows": len(certificate.get("reactions", [])),
        "formula_charge_audited": len(audited),
        "stoichiometrically_balanced": balanced,
        "stoichiometrically_unbalanced": len(audited) - balanced,
        "finite_formula_residuals": residual,
        "reactions": audited,
        "kinetics_supplied": False,
        "compartment_state_supplied": False,
        "measured_flux_promoted": False,
        "disease_mechanism_promoted": False,
        "residuals": [
            "formula-incomplete/polymeric/R-group reactions stay outside finite formula audit",
            "kinetic-law parameters not supplied",
            "compartment-specific BH4/BH2 amounts not supplied",
            "simultaneous enzyme demand and transport/oxidation flux not supplied",
            "whole-system FluxBalanceWitness not paid",
            "disease-level causal transition not paid",
        ],
    }


def write_outputs(result: dict, prefix: Path) -> None:
    prefix.parent.mkdir(parents=True, exist_ok=True)
    prefix.with_suffix(".json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    reaction_rows = result.get("reactions")
    if isinstance(reaction_rows, list):
        with prefix.with_suffix(".csv").open("w", newline="", encoding="utf-8") as handle:
            writer = csv.DictWriter(
                handle,
                fieldnames=["rhea_id", "stoichiometrically_balanced", "substrate_charge", "product_charge"],
            )
            writer.writeheader()
            for row in reaction_rows:
                writer.writerow({key: row.get(key) for key in writer.fieldnames})
    else:
        with prefix.with_suffix(".csv").open("w", newline="", encoding="utf-8") as handle:
            writer = csv.DictWriter(handle, fieldnames=["side", "coefficient", "chebi_id", "name", "formula", "charge"])
            writer.writeheader()
            writer.writerows(result["participants"])
    lines = [
        "# BH4 reaction-network receipt",
        "",
        f"- kinetics supplied: `{str(result['kinetics_supplied']).lower()}`",
        f"- measured flux promoted: `{str(result['measured_flux_promoted']).lower()}`",
        f"- disease mechanism promoted: `{str(result['disease_mechanism_promoted']).lower()}`",
    ]
    if "rhea_id" in result:
        lines.extend([
            f"- reaction: {result['rhea_id']}",
            f"- stoichiometrically balanced: `{str(result['stoichiometrically_balanced']).lower()}`",
        ])
    else:
        lines.extend([
            f"- reaction rows: {result['reaction_identity_rows']}",
            f"- finite formula/charge audits: {result['formula_charge_audited']}",
            f"- balanced audits: {result['stoichiometrically_balanced']}",
            f"- finite-formula residuals: {len(result['finite_formula_residuals'])}",
        ])
    lines.extend(["", "## Residuals", *[f"- {item}" for item in result["residuals"]]])
    prefix.with_suffix(".md").write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--qdpr", action="store_true")
    mode.add_argument("--certificate", type=Path, metavar="PATH")
    parser.add_argument("--output-prefix", type=Path)
    args = parser.parse_args()
    result = audit_reaction(QDPR) if args.qdpr else audit_certificate(args.certificate)
    if args.output_prefix:
        write_outputs(result, args.output_prefix)
    else:
        print(json.dumps(result, indent=2, sort_keys=True))
    if args.qdpr:
        return 0 if result["stoichiometrically_balanced"] else 3
    return 3 if result["stoichiometrically_unbalanced"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
