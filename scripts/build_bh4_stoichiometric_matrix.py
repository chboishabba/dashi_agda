#!/usr/bin/env python3
"""Build a deterministic BH4 panel stoichiometric matrix from a Rhea certificate.

Input is the `dashi.rhea-chebi-bh4-panel.v2` certificate produced by
`acquire_rhea_chebi_bh4_reactions.py`. Only formula/charge-ready reactions are
placed in the finite matrix. Incomplete/polymeric/R-group reactions are retained
as residuals, never represented by an all-zero column.
"""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path


def participant_key(p: dict) -> str:
    return str(p.get("chebi_id") or p.get("compound_uri") or p.get("name") or "unidentified")


def signed_coefficient(p: dict) -> int:
    coeff = int(str(p.get("coefficient", 1)))
    if coeff < 0:
        raise ValueError(f"negative stoichiometric coefficient: {coeff}")
    side = p.get("side")
    if side == "substrate":
        return -coeff
    if side == "product":
        return coeff
    raise ValueError(f"unsupported reaction side: {side!r}")


def build_matrix(certificate: dict) -> dict:
    finite: list[dict] = []
    residuals: list[dict] = []
    for reaction in certificate.get("reactions", []):
        rid = str(reaction.get("rhea_id", "unidentified"))
        participants = reaction.get("participants", [])
        if not reaction.get("formula_charge_ready") or not participants:
            residuals.append({"rhea_id": rid, "reason": "finite participant formula/charge receipt incomplete"})
            continue
        try:
            entries = [(participant_key(p), signed_coefficient(p)) for p in participants]
        except (TypeError, ValueError) as exc:
            residuals.append({"rhea_id": rid, "reason": str(exc)})
            continue
        finite.append({"rhea_id": rid, "participants": participants, "entries": entries})

    species_index = sorted({species for reaction in finite for species, _ in reaction["entries"]})
    reaction_index = sorted(reaction["rhea_id"] for reaction in finite)
    species_position = {species: i for i, species in enumerate(species_index)}
    reaction_position = {rid: j for j, rid in enumerate(reaction_index)}
    matrix = [[0 for _ in reaction_index] for _ in species_index]

    by_reaction = {reaction["rhea_id"]: reaction for reaction in finite}
    for rid in reaction_index:
        j = reaction_position[rid]
        for species, coeff in by_reaction[rid]["entries"]:
            matrix[species_position[species]][j] += coeff

    columns = [
        {
            "rhea_id": rid,
            "nonzero_entries": [
                {"species": species_index[i], "signed_coefficient": matrix[i][j]}
                for i in range(len(species_index))
                if matrix[i][j] != 0
            ],
        }
        for j, rid in enumerate(reaction_index)
    ]

    return {
        "schema": "dashi.bh4-stoichiometric-matrix.v1",
        "source_certificate_schema": certificate.get("schema"),
        "species_index": species_index,
        "reaction_index": reaction_index,
        "matrix": matrix,
        "columns": columns,
        "finite_reaction_count": len(reaction_index),
        "finite_species_count": len(species_index),
        "finite_formula_residuals": residuals,
        "external_exchange": [],
        "promotion_boundary": {
            "matrix_creates_kinetics": False,
            "missing_reaction_becomes_zero_column": False,
            "internal_matrix_includes_external_exchange": False,
            "matrix_creates_disease_mechanism": False,
        },
    }


def write_outputs(result: dict, prefix: Path) -> None:
    prefix.parent.mkdir(parents=True, exist_ok=True)
    prefix.with_suffix(".json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    with prefix.with_suffix(".csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(["species", *result["reaction_index"]])
        for species, row in zip(result["species_index"], result["matrix"]):
            writer.writerow([species, *row])
    lines = [
        "# BH4 stoichiometric matrix receipt",
        "",
        f"- finite species: {result['finite_species_count']}",
        f"- finite reactions: {result['finite_reaction_count']}",
        f"- formula/incomplete residuals: {len(result['finite_formula_residuals'])}",
        "- external exchange columns in S: `0`",
        "",
        "Missing or non-finite reactions are residuals, not zero columns.",
    ]
    prefix.with_suffix(".md").write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--output-prefix", type=Path)
    args = parser.parse_args()
    result = build_matrix(json.loads(args.certificate.read_text(encoding="utf-8")))
    if args.output_prefix:
        write_outputs(result, args.output_prefix)
    else:
        print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
