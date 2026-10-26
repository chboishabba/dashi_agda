#!/usr/bin/env python3
"""Read-only DMT motif cross-source hyperfabric (typed evidence fibre audit).

Runtime PROJECTION of existing DASHI.Reasoning.TypedHyperfabricCore,
DASHI.Core.EvidenceHyperfabricExact and source-world selective reopening.
Not an extracted Agda program, neural inference or legal permission grant.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SPEC = ROOT / "Docs/receipts/DMTMotifObservationHyperfabric20261025.json"
WORLD = ROOT / "Docs/receipts/DMT2023SourceWorld.json"
EROWID = ROOT / "Docs/receipts/DMTRecurringMotifErowidPriorArtBridge20261025.json"
FORMAL_SOURCE = ROOT / "DASHI/Biology/DMTMotifObservationHyperfabricExact.agda"
AGGREGATE = ROOT / "DASHI/Cognition/ConsciousRealismDMTEverything.agda"
PUBLISHED = "present_source_statement"
CONSTRUCTED = "present_constructed_not_empirical"
MISSING = "notLocated"
ALLOWED_STATUSES = {PUBLISHED, CONSTRUCTED, MISSING}
EXPERIMENTAL_ROLES = {
    "measured_temporal", "cross_study_paired",
    "original_study_reproduction", "theory_discriminator",
    "prospective_anomalous_channel",
}


def load(path=SPEC):
    return json.loads(Path(path).read_text(encoding="utf8"))


def _source_map(source_world):
    return {a["id"]: a["status"] for a in source_world["artifacts"]}


def validate(hyperfabric, source_world, erowid):
    if hyperfabric.get("schema") != "dashi-dmt-motif-hyperfabric-v1":
        raise ValueError("Invalid DMT observation hyperfabric schema")
    o = hyperfabric["canonical_origin"]
    if o["source_world"] != "Docs/receipts/DMT2023SourceWorld.json":
        raise ValueError("Hyperfabric detached from canonical source world")
    if o["erowid_prior_art"] != "Docs/receipts/DMTRecurringMotifErowidPriorArtBridge20261025.json":
        raise ValueError("Hyperfabric detached from original Erowid prior art")
    if erowid["original_published_research"]["doi"] != o["erowid_published_doi"]:
        raise ValueError("Erowid author source citation no longer matches")
    if erowid["raw_data_governance"]["raw_report_corpus_acquired"] is not False:
        raise ValueError("Raw Erowid reports cannot be silently promoted")
    if erowid["raw_data_governance"]["permission_obtained"] is not False:
        raise ValueError("Original Erowid rights scope not established")
    if erowid["no_empirical_markov_kernel_fitted"] is not True:
        raise ValueError("Source chronology/kernel cannot be inferred from report fractions")
    a = _source_map(source_world)
    cross = {
        "original_voxel_input": "original_preprocessed_voxel_nifti",
        "original_motion_qc": "original_static_fd",
        "original_executable_state": "effective_static_gfc_workspace",
        "original_data_authority": "data_use_review",
        "sanders_individual_phase": "sanders_phase_data",
        "cohort_crosswalk": "participant_lineage",
    }
    for site_id, art in cross.items():
        if a.get(art) != MISSING:
            raise ValueError("Original-world evidence changed; re-evaluate " + site_id)
    if a.get("sanders_article") != "present":
        raise ValueError("Sanders publication source not located")
    if a.get("primary_paper") != "present":
        raise ValueError("Original PNAS publication source not located")
    sites = hyperfabric.get("sites", [])
    edges = hyperfabric.get("edges", [])
    by_site = {x["id"]: x for x in sites}
    by_edge = {x["id"]: x for x in edges}
    if len(by_site) != len(sites) or len(by_edge) != len(edges):
        raise ValueError("Duplicate site or consumer edge")
    if len(sites) != 15 or len(edges) != 8:
        raise ValueError("Typed source-site graph cardinality changed")
    for site in sites:
        if site["state"] not in ALLOWED_STATUSES:
            raise ValueError("Unrecognized source fibre state")
        if not site.get("kind") or not site.get("unit") or not site.get("provenance"):
            raise ValueError("Missing source-site measurement/provenance fibre")
        if not site.get("rights") or not site.get("measurement"):
            raise ValueError("Missing rights or observational scope")
        if site["kind"] == "governance_receipt" and site["state"] != MISSING:
            raise ValueError("Governance source falsely recorded as authorized")
    if (by_site["erowid_category"]["state"] != PUBLISHED or
        by_site["existing_motif_operator"]["state"] != CONSTRUCTED or
        by_site["sanders_published_phase"]["state"] != PUBLISHED):
        raise ValueError("Original documentary/toy status changed")
    if any(x["state"] != MISSING for x in sites if x["id"] not in
           ("erowid_category", "existing_motif_operator", "sanders_published_phase")):
        raise ValueError("Unlocated empirical source has been promoted")
    for edge in edges:
        needs = edge.get("requires", [])
        if not needs or len(set(needs)) != len(needs) or not set(needs) <= by_site.keys():
            raise ValueError("Dangling or duplicate source evidence on edge")
        if not edge.get("provenance") or not edge.get("max_claim"):
            raise ValueError("No attributed edge or claim ceiling")
    for e in hyperfabric.get("forbidden_edges", []):
        if e["from"] not in by_site and e["from"] not in by_edge:
            raise ValueError("Unknown forbidden source")
        if e["to"] not in by_edge and e["to"] != "M4_independent_external_ontology":
            raise ValueError("Unknown forbidden consumer")
        if e["from"] in by_site and e["to"] in by_edge and (
            e["from"] in by_edge[e["to"]]["requires"]
        ):
            raise ValueError("Forbidden direct source-to-consumer incidence")
    must_forbid = {("erowid_category", "e_report_temporal_transition"),
                   ("erowid_category", "e_original_neural_replay"),
                   ("existing_motif_operator", "e_mechanistic_M2_test"),
                   ("sanders_published_phase", "e_paired_temporal_claim")}
    observed = {(e["from"], e["to"]) for e in hyperfabric["forbidden_edges"]}
    if not must_forbid <= observed:
        raise ValueError("Critical cross-fibre non-promotion edge missing")
    restrictions = hyperfabric["no_auto_promotions"]
    if not restrictions or not all(value is True for value in restrictions.values()):
        raise ValueError("Observation-fibre epistemic boundaries changed")
    if not FORMAL_SOURCE.exists() or not AGGREGATE.exists():
        raise ValueError("Focused Agda hyperfabric adapter missing")
    agda = FORMAL_SOURCE.read_text(encoding="utf8")
    aggregate = AGGREGATE.read_text(encoding="utf8")
    for owner in (
        "DASHI.Reasoning.TypedHyperfabricCore",
        "DASHI.Core.EvidenceHyperfabricExact",
        "DASHI.Core.ObserverRefinementLatticeExact",
        "DASHI.Biology.VisualMotifTransitionOperator",
    ):
        if owner not in agda:
            raise ValueError("Existing formal hyperfabric owner not actually reused: " + owner)
    if ("noTransitionReconstructionFromCoarseFrequency" not in agda or
        "reportTemporalNeedsPermission" not in agda or
        "DMTMotifObservationHyperfabricExact" not in aggregate):
        raise ValueError("Finite source-specific hyperfabric bridge not registered")
    return True


def classify_edge(edge, sites):
    by_site = {s["id"]: s for s in sites}
    unavailable = [k for k in edge["requires"] if by_site[k]["state"] == MISSING]
    if unavailable:
        return {"id": edge["id"], "status": "blocked_by_source_fibres",
                "missing_sites": unavailable, "max_claim": edge["max_claim"],
                "empirical_claim_reproduced": False}
    if edge["role"] in EXPERIMENTAL_ROLES:
        # Even a list of documentarily present sources would not prove aligned
        # measurements or independent reproduction.
        raise ValueError("Experimental edge admitted without measured source evidence")
    state = {
        "descriptive": "published_descriptive_only",
        "formal_not_empirical": "constructed_toy_only",
        "comparison_without_subject_join": "published_cross_study_hypothesis_only",
    }.get(edge["role"])
    if state is None:
        raise ValueError("Unknown nonempirical edge role")
    return {"id": edge["id"], "status": state,
            "missing_sites": [], "max_claim": edge["max_claim"],
            "empirical_claim_reproduced": False}


def candidate_reopening(hyperfabric, site_id):
    # A dry-run must also validate the exact currently admitted source status:
    # it may not be used with a forged report, permission or cohort object.
    validate(hyperfabric, load(WORLD), load(EROWID))
    sites = {s["id"]: s for s in hyperfabric["sites"]}
    if site_id not in sites:
        raise ValueError("Unknown fibre site")
    if sites[site_id]["state"] != MISSING:
        raise ValueError("Only notLocated source sites can be candidates")
    affected = [
        {"edge": e["id"],
         "remaining_unlocated": [i for i in e["requires"]
                                 if i != site_id and sites[i]["state"] == MISSING],
         "claim_immediately_admitted": False}
        for e in hyperfabric["edges"] if site_id in e["requires"]
    ]
    return {"candidate_site": site_id, "source_state_after": MISSING,
            "world_mutated": False, "rights_or_measurement_verified": False,
            "would_reopen_only": affected, "ontology_inferred": False}


def audit(hyperfabric=None, source_world=None, erowid=None):
    hyperfabric = load() if hyperfabric is None else hyperfabric
    source_world = load(WORLD) if source_world is None else source_world
    erowid = load(EROWID) if erowid is None else erowid
    validate(hyperfabric, source_world, erowid)
    edges = [classify_edge(e, hyperfabric["sites"])
             for e in hyperfabric["edges"]]
    return {
        "status": "read_only_typed_observation_fibres",
        "sites": len(hyperfabric["sites"]), "hyperedges": len(edges),
        "published_or_constructed_admitted": [
            e["id"] for e in edges if e["status"] != "blocked_by_source_fibres"
        ],
        "blocked_edges": {
            e["id"]: e["missing_sites"] for e in edges
            if e["status"] == "blocked_by_source_fibres"
        },
        "no_raw_erowid_data_acquired": True,
        "no_report_chronology_measured": True,
        "no_cross_cohort_same_person_join": True,
        "no_original_neural_replay": True,
        "no_external_agent_inferred": True,
        "forbidden_edges": len(hyperfabric["forbidden_edges"]),
        "source_identification": hyperfabric["canonical_origin"],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candidate-site", help="Preview source-specific selective reopening")
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    h = load()
    result = candidate_reopening(h, args.candidate_site) if args.candidate_site else audit(h)
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.out:
        args.out.write_text(rendered, encoding="utf8")
    else:
        print(rendered)


if __name__ == "__main__":
    main()
