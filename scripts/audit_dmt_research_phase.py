#!/usr/bin/env python3
"""Consumer-relative DMT acquisition + model-card audit; read-only.

Uses the *existing* DMT source-world search implementation. Dewey, DOI and QID
are navigation metadata, never source-truth or evidence permissions. Report
readiness is not experimental reproduction, fitted modelling or preregistration.
"""
from __future__ import annotations
import argparse
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DOSSIER = ROOT / "Docs/receipts/DMT2023DeweyIbrahimAcquisitionDecision20261024.json"
CARDS = ROOT / "Docs/receipts/DMTRestrictedModelCards20261024.json"
SOURCE_ENGINE = ROOT / "scripts/dmt_source_world_search.py"
REQUIRED_MODELS = ("M0", "M1", "M2")
EXPECTED_CONSUMERS = ("c_static_reproduction", "c_temporal_replication")


def _load_engine():
    spec = importlib.util.spec_from_file_location("dmt_source_world_search", SOURCE_ENGINE)
    engine = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(engine)
    return engine


def _ids(xs, *, label):
    ids = [x["id"] for x in xs]
    if len(ids) != len(set(ids)):
        raise ValueError("Duplicate " + label + " IDs")
    return set(ids)


def validate_research_contract(world, dossier, cards):
    source_engine = _load_engine()
    source_engine.validate_world(world)
    if dossier.get("schema") != "dashi-dmt-acquisition-decision-v1":
        raise ValueError("Unsupported acquisition dossier schema")
    if cards.get("schema") != "dashi-dmt-restricted-model-cards-v1":
        raise ValueError("Unsupported model-card schema")
    if dossier.get("world_path") != "Docs/receipts/DMT2023SourceWorld.json":
        raise ValueError("Unpinned research source-world path")
    if cards.get("source_world") != dossier["world_path"]:
        raise ValueError("Model cards do not use the same source world")
    if cards.get("acquisition_dossier") != "Docs/receipts/DMT2023DeweyIbrahimAcquisitionDecision20261024.json":
        raise ValueError("Model cards do not use the declared primary-acquisition dossier")
    if not dossier.get("no_outreach") or not dossier.get("no_data_fetched"):
        raise ValueError("Acquisition dossier must not invent correspondence or data access")
    if cards.get("status") != "pre_empirical_design_only" or cards.get("empirical_predictions_tested") is not False:
        raise ValueError("Model-card design must not assert fitted empirical results")
    if cards.get("primary_study_doi") != "10.1073/pnas.2218949120":
        raise ValueError("Unexpected original study DOI")
    actions = {x["id"]: x for x in world["actions"]}
    artifacts = {x["id"]: x for x in world["artifacts"]}
    claims = {x["id"]: x for x in world["claims"]}
    sources = {x["id"]: x for x in world["sources"]}
    if not set(EXPECTED_CONSUMERS) <= claims.keys():
        raise ValueError("Lost core empirical consumer")
    for entry in dossier["source_search"]:
        if entry["world_action"] not in actions:
            raise ValueError("Acquisition route has no actual world action: " + entry["id"])
        act = actions[entry["world_action"]]
        if entry["source_root"] not in sources:
            raise ValueError("Unknown primary source role")
        if set(entry["missing_artifacts"]) != set(act["targets"]):
            raise ValueError("Acquisition advertised targets diverge from action: " + entry["id"])
        if not set(entry["target_consumers"]) <= claims.keys():
            raise ValueError("Acquisition target consumer missing from world")
        if not entry.get("completion_test") or not entry.get("producer"):
            raise ValueError("Acquisition without source-specific completion test")
        for consumer in entry["target_consumers"]:
            if not set(entry["missing_artifacts"]) & set(claims[consumer]["requires"]):
                raise ValueError("False action/consumer fanout: " + entry["id"] + " -> " + consumer)
        if all(artifacts[x]["status"] == "present" for x in entry["missing_artifacts"]):
            if "unlocated" in entry["status"] or "gated" in entry["status"]:
                raise ValueError("Dossier stale relative to paid source coordinates")
    if _ids(dossier["source_search"], label="acquisition") != {
        "motion_qc", "rights", "effective_code", "voxel_atlas",
        "sanders_phases", "public_mat_exploratory",
    }:
        raise ValueError("Missing an exact acquisition lane")
    for item in dossier["known_impossibilities"]:
        c = claims[item["consumer"]]
        if not any(artifacts[x]["status"] == "knownAbsent" for x in c["requires"]):
            raise ValueError("Tree-scoped impossibility not supported by negative source receipt")
        if item["status"] != "source_scope_blocked":
            raise ValueError("Known-absent not distinguished from globally missing")
    for lens in dossier["navigation"]["subject_lenses"]:
        if not lens.get("label") or not lens.get("queries"):
            raise ValueError("Dewey navigation lens must have bounded source queries")
        if lens["dewey"] != "unresolved" or lens["qid"] != "unresolved":
            raise ValueError("DDC/QID requires independent verified source receipt")
    roots = {source["lineage_root"] for source in sources.values()}
    if len(roots) != 3 or not {"pnas2023", "sanders2026", "brainit2026"} <= roots:
        raise ValueError("Source genealogy changed; review subject independence before promotion")
    if len(cards["models"]) != 3 or tuple(x["id"] for x in cards["models"]) != REQUIRED_MODELS:
        raise ValueError("M0/M1/M2 benchmark family not frozen in specified order")
    common = cards["shared_contract"]
    observables = common["observables"]
    if (len(observables) < 4 or len(set(observables)) != len(observables) or
        set(common["same_outcome_dictionary_for"]) != set(REQUIRED_MODELS) or
        common.get("same_preprocessing_and_missingness") is not True):
        raise ValueError("Model comparison lacks same observables and preprocessing")
    split = common["same_split"]
    if split.get("unit") != "whole_subject" or "together" not in split.get("pairing", ""):
        raise ValueError("Subject paired-condition split not preserved")
    if split.get("seed_status") != "to_predeclare_before_receipt":
        raise ValueError("Cannot claim seeded/pre-registered data split yet")
    for m in cards["models"]:
        if m.get("observation_dictionary") != "shared_contract.observables" or m.get("data_ready") is not False:
            raise ValueError("Model diverges from matched observation dictionary or invents data")
        for k in ("predictions", "falsification", "nonpromotion", "fitted_only_in_training"):
            if not m.get(k):
                raise ValueError("Incomplete model discrimination contract: " + m["id"])
    m2 = cards["models"][2]
    if "fixed Q" not in m2["transition"] or "Markov" not in m2["nonpromotion"]:
        raise ValueError("M2 lacks fixed-Q versus generic Markov no-uniqueness boundary")
    external = cards["independent_consumers"]
    if _ids(external, label="external experimental consumer") != {"M3", "M4"}:
        raise ValueError("Information channel and ontology consumers conflated")
    for c in external:
        if not c["not_same_outcome_as_M0_M2"] or not c["requires"] or "no_current" not in c["status"] and "not_approved" not in c["status"]:
            raise ValueError("Unapproved M3/M4 experiment promoted to evidence")
    if "phase matrices" not in dossier["source_search"][4]["verified_locator_detail"]:
        raise ValueError("Sanders source-phase distinction lost")
    return True


def summary(world, dossier, cards):
    validate_research_contract(world, dossier, cards)
    engine = _load_engine()
    claims = engine.claim_status(world)
    actions = engine.action_candidates(world)
    selected = [x for x in actions if x["pareto"]]
    phase_a = {
        "phase_0": "foundation_substantially_paid; regression execution reported separately from empirical-model tests",
        "phase_1": "active_primary_evidence_acquisition",
        "phase_2": "source_gated_original_reproduction_and_design_only_M0_M1_M2",
        "phase_3": "held_out_empirical_models_not_admitted",
        "phase_4": "concealed_target_study_not_approved",
        "phase_5": "synthesis_pending_measurement_and_attribution",
    }
    return {
        "status": "read_only_source_and_design_audit",
        "phase_status": phase_a,
        "source_records": len(world["sources"]),
        "bibliographic_provenance_roots_not_cohort_replicates": len(
            set(x["lineage_root"] for x in world["sources"])
        ),
        "evidence_status_counts": {
            value: sum(x["status"] == value for x in world["artifacts"])
            for value in ("present", "notLocated", "knownAbsent")
        },
        "claims_by_state": {
            state: sum(c["state"] == state for c in claims)
            for state in ("source_attested_only", "acquisition_blocked", "source_scope_blocked")
        },
        "live_research_frontier": [{
            "id": a["id"], "targets": a["potential_artifacts"],
            "candidate_claims": a["potential_consumer_ids"],
            "cost_band": a["cost_band"], "access_risk": a["access_risk"]
        } for a in selected],
        "conditional_static_gfc_route": engine.hypothetical_plan(
            world, "c_static_reproduction"
        )["hypothetical_actions"],
        "public_mat_only_original_replay": engine.hypothetical_plan(
            world, "c_public_mat_reproduces_original_static"
        )["status"],
        "frozen_model_families": [m["id"] for m in cards["models"]],
        "independent_unapproved_consumers": [x["id"] for x in cards["independent_consumers"]],
        "data_fetched": False, "original_fmri_result_reproduced": False,
        "data_use_permission_granted": False, "pre_registration_completed": False,
        "source_specific_tests_are_not_scientific_results": True,
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--world", type=Path, default=ROOT / "Docs/receipts/DMT2023SourceWorld.json")
    p.add_argument("--dossier", type=Path, default=DOSSIER)
    p.add_argument("--models", type=Path, default=CARDS)
    p.add_argument("--out", type=Path)
    args = p.parse_args()
    w, d, c = [json.loads(path.read_text(encoding="utf8"))
               for path in (args.world, args.dossier, args.models)]
    result = json.dumps(summary(w, d, c), indent=2, sort_keys=True) + "\n"
    if args.out:
        args.out.write_text(result, encoding="utf8")
    else:
        print(result)


if __name__ == "__main__":
    main()
