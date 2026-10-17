#!/usr/bin/env python3
"""Prepare a fail-closed per-reaction flux-payment ledger.

Consumes the ranked kinetic candidate artifact and emits, for every finite Rhea
column, the strongest available evidence class plus the specific normalization
and context obligations that still block use as a solver flux interval.

This script deliberately does NOT calculate a reaction-flux bound. Assay
Vmax/specific-activity values normalized by protein mass are not intracellular
compartment fluxes and require an abundance/mass-basis bridge; kcat values also
require an independent enzyme-abundance/state coordinate before they can define
capacity.
"""
from __future__ import annotations
import argparse, json, re
from pathlib import Path
from typing import Any


def _unit_text(unit: Any) -> str:
    if isinstance(unit, dict):
        return " ".join(str(unit.get(k) or "") for k in ("name", "symbol", "term", "id")).strip().lower()
    return str(unit or "").strip().lower()


def _is_per_mass(unit: Any) -> bool:
    text = _unit_text(unit)
    return bool(re.search(r"(?:/|per\s*)(?:mg|g)\b", text) or "mg^-1" in text or "g^-1" in text)


def _is_per_time(unit: Any) -> bool:
    text = _unit_text(unit)
    return any(tok in text for tok in ("/s", "s^-1", "sec^-1", "second^-1", "/min", "min^-1", "/h", "h^-1"))


def _is_concentration_rate(unit: Any) -> bool:
    text = _unit_text(unit)
    return any(tok in text for tok in ("mol/l", "molar", "mol l", "m/l", "mmol/l", "umol/l", "µmol/l")) and _is_per_time(unit)


def evidence_class(reaction: dict) -> str:
    if not reaction.get("candidate_count"): return "primary-literature-gap"
    if int(reaction.get("direct_rate_candidate_count") or 0) > 0: return "assay-specific-capacity"
    if int(reaction.get("capacity_candidate_count") or 0) > 0: return "turnover-capacity"
    return "kinetic-shape-only"


def reaction_requirements(reaction: dict) -> dict:
    klass = evidence_class(reaction)
    top = list(reaction.get("top_candidates") or [])
    first = top[0] if top else {}
    unit = first.get("unit")
    per_mass = _is_per_mass(unit)
    enzyme_abundance_required = klass == "turnover-capacity" or (klass == "assay-specific-capacity" and per_mass)
    normalization_bridge_required = klass in {"assay-specific-capacity", "turnover-capacity"}
    assay_condition_translation_required = True
    magnitude_anchor_missing = klass in {"kinetic-shape-only", "primary-literature-gap"}
    if klass == "assay-specific-capacity" and per_mass:
        reason = "specific activity is normalized by assay protein mass; compartment enzyme/protein abundance and volume/mass bridge are required"
    elif klass == "assay-specific-capacity" and _is_concentration_rate(unit):
        reason = "assay concentration-rate basis still requires same-compartment/state and assay-condition translation"
    elif klass == "assay-specific-capacity":
        reason = "assay rate basis must be translated into the solver's common compartment flux unit"
    elif klass == "turnover-capacity":
        reason = "kcat/turnover requires enzyme abundance/activity state before Vmax = kcat*[E] can define a capacity"
    elif klass == "kinetic-shape-only":
        reason = "Km/Kd/Ki-like evidence constrains kinetic shape, not flux magnitude; a rate/capacity anchor is still required"
    else:
        reason = "SABIO has no direct candidate for this finite reaction; primary literature must be adjudicated before quantitative translation"
    gates = {
        "assay_reaction_identity_paid": False,
        "same_object_compartment_time_paid": False,
        "normalized_solver_flux_unit_paid": False,
        "kinetic_to_flux_translation_paid": False,
    }
    return {
        "rhea_id": reaction.get("rhea_id"),
        "evidence_class": klass,
        "candidate_count": int(reaction.get("candidate_count") or 0),
        "direct_rate_candidate_count": int(reaction.get("direct_rate_candidate_count") or 0),
        "capacity_candidate_count": int(reaction.get("capacity_candidate_count") or 0),
        "enzyme_abundance_required": enzyme_abundance_required,
        "normalization_bridge_required": normalization_bridge_required,
        "assay_condition_translation_required": assay_condition_translation_required,
        "magnitude_anchor_missing": magnitude_anchor_missing,
        "top_candidate_unit": unit,
        "top_candidate_per_mass_normalized": per_mass,
        "normalization_reason": reason,
        "payment_gates": gates,
        "steady_state_flux_bound_payable": all(gates.values()) and not magnitude_anchor_missing,
        "top_candidates": top,
    }


def prepare(ranking: dict) -> dict:
    rows = [reaction_requirements(r) for r in ranking.get("top_candidates_by_reaction", [])]
    classes: dict[str, int] = {}
    for row in rows: classes[row["evidence_class"]] = classes.get(row["evidence_class"], 0) + 1
    return {
        "schema": "dashi.bh4-flux-payment-preparation.v1",
        "source_ranking_schema": ranking.get("schema"),
        "finite_reaction_count": len(rows),
        "evidence_class_counts": dict(sorted(classes.items())),
        "enzyme_abundance_required_reactions": [r["rhea_id"] for r in rows if r["enzyme_abundance_required"]],
        "normalization_bridge_required_reactions": [r["rhea_id"] for r in rows if r["normalization_bridge_required"]],
        "magnitude_anchor_missing_reactions": [r["rhea_id"] for r in rows if r["magnitude_anchor_missing"]],
        "payable_reaction_count": sum(bool(r["steady_state_flux_bound_payable"]) for r in rows),
        "reactions": rows,
        "promotion_boundary": {
            "rate_candidate_creates_intracellular_flux": False,
            "specific_activity_creates_compartment_flux": False,
            "per_mass_rate_creates_flux_without_abundance_bridge": False,
            "kcat_creates_flux_without_abundance": False,
            "shape_parameter_creates_magnitude_bound": False,
            "primary_literature_creates_flux_bound": False,
            "missing_gate_defaults_paid": False,
        },
    }


def main() -> int:
    p=argparse.ArgumentParser(); p.add_argument("--ranking",type=Path,required=True); p.add_argument("-o","--output",type=Path); a=p.parse_args()
    result=prepare(json.loads(a.ranking.read_text(encoding="utf-8"))); text=json.dumps(result,indent=2,sort_keys=True)+"\n"
    if a.output: a.output.parent.mkdir(parents=True,exist_ok=True); a.output.write_text(text,encoding="utf-8")
    else: print(text,end="")
    return 0

if __name__ == "__main__": raise SystemExit(main())
