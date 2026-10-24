#!/usr/bin/env python3
"""Read-only source-world proof-search over attributed primary objects.

This is an execution projection of EXISTING DASHI owner semantics:
EvidenceAcquisitionSelectiveReopeningExact, SourceConditionedObservationExact,
CostedResidualInformationChoiceExact, ProofSearchLeastPrivilegeAdmissionExact
and IbrahimSnowballDependencyNDimLocalGlobalProofSearchBidiExact.

The search computes COUNTERFACTUAL SOURCE ACQUISITION PLANS, not evidence,
human data, legal permission, experimental replication or kernel proofs.
No network, email, file mutation or third-party access.
"""
from __future__ import annotations
import argparse
import json
import re
from pathlib import Path

DEFAULT_WORLD = (Path(__file__).resolve().parents[1] /
                 "Docs/receipts/DMT2023SourceWorld.json")
STATES = {"present", "notLocated", "knownAbsent"}
STATUS_GRADE = {"source_claim", "source_metadata", "subject_specific",
                "research_access", "empirical", "ontology"}


def load_world(path: Path = DEFAULT_WORLD) -> dict:
    world = json.loads(path.read_text(encoding="utf8"))
    validate_world(world)
    return world


def validate_world(world: dict) -> None:
    if world.get("schema") != "dashi-source-world-v1":
        raise ValueError("Unrecognized source-world schema")
    if world.get("safety", {}).get("send_email") is not False:
        raise ValueError("External contact/actuation forbidden")
    if world["safety"].get("autopromote_ontology") is not False:
        raise ValueError("Ontology cannot auto-promote")
    sources = {s["id"]: s for s in world["sources"]}
    artifacts = {a["id"]: a for a in world["artifacts"]}
    claims = {c["id"]: c for c in world["claims"]}
    actions = {a["id"]: a for a in world["actions"]}
    for name, original, keyed in (
        ("source", world["sources"], sources),
        ("artifact", world["artifacts"], artifacts),
        ("consumer", world["claims"], claims),
        ("action", world["actions"], actions),
    ):
        if len(original) != len(keyed):
            raise ValueError("Duplicate " + name + " ID")
    for source in sources.values():
        if not source.get("author") or not source.get("title") or not source.get("url"):
            raise ValueError("Unattributed source " + source["id"])
        if not source.get("lineage_root"):
            raise ValueError("Source requires an explicit provenance-root key")
    # Source-record count differs from the number of independent empirical
    # roots. A primary paper, its author script, and a reuse study must never
    # be counted as three independent participant acquisitions.
    # These are bibliographic provenance roots, NOT necessarily independent
    # participant cohorts. Sanders participant overlap is unverified.
    distinct_roots = {v["lineage_root"] for v in sources.values()}
    if (world.get("counts", {}).get("distinct_lineage_roots") != len(distinct_roots)
            or not set(distinct_roots) <= sources.keys()):
        raise ValueError("Incorrect independent source-root count")
    namespace = next((a for a in world["artifacts"]
                      if a["id"] == "source_subject_namespace"), None)
    if namespace is not None:
        listed = namespace.get("subject_ids")
        if (not isinstance(listed, list) or len(listed) != 20
                or len(set(listed)) != 20
                or namespace.get("git_blob_sha1") != sources["pnas_static_script"].get("git_blob_sha1")):
            raise ValueError("Source manuscript subject IDs not pinned to author script")
    for edge in world["source_dependencies"]:
        if edge["from"] not in sources or edge["to"] not in sources:
            raise ValueError("Dangling provenance source edge")
        if edge["type"] == "independent_replication":
            if sources[edge["from"]]["lineage_root"] == sources[edge["to"]]["lineage_root"]:
                raise ValueError("Shared cohort is not an independent replication")
    for art in artifacts.values():
        if art["status"] not in STATES or art["source"] not in sources:
            raise ValueError("Invalid artifact status or source link")
        if art["status"] == "present" and not art.get("locator"):
            raise ValueError("A present artifact needs a specific locator")
        if art["status"] == "knownAbsent" and not art.get("negative_search_receipt"):
            raise ValueError("Known absence requires a checked negative-search receipt")
    for claim in claims.values():
        if claim["grade"] not in STATUS_GRADE or not claim.get("requires"):
            raise ValueError("Invalid claim or missing evidence obligations")
        if not set(claim["requires"]) <= artifacts.keys():
            raise ValueError("Claim has nonexistent evidence obligation")
    for act in actions.values():
        if not set(act["needs"]) <= artifacts.keys():
            raise ValueError("Action has a missing prerequisite")
        if not set(act["targets"]) <= artifacts.keys():
            raise ValueError("Action has nonexistent potential evidence output")
        if any(artifacts[x]["status"] == "knownAbsent" for x in act["targets"]):
            raise ValueError("Scoped knownAbsent artifact cannot become a new source via this action")
        if act["cost_band"] not in (1, 2, 3, 4) or act["access_risk"] not in (1, 2, 3, 4):
            raise ValueError("Costs/risks must remain declared ordinal policy bands")
        if any(artifacts[x]["status"] == "knownAbsent" for x in act["needs"]):
            raise ValueError("Route may not silently pretend known-absent inputs exist")
    tree = world["observed_git_tree"]
    if tree["source_commit"] != sources["pnas_gitrepo"]["git_commit"]:
        raise ValueError("Source tree not revision-locked")
    # Guard against a stale or copied world inventing a different source file
    # inventory: its independent source-tree receipt must match exactly.
    canonical_path = (Path(__file__).resolve().parents[1] /
                      "Docs/receipts/DMTImagingPinnedSourceTree20261024.json")
    canonical = json.loads(canonical_path.read_text(encoding="utf8"))
    if (tree["source_commit"] != canonical["source_commit"]
            or tree["source_tree_sha1"] != canonical["source_tree_sha1"]
            or tree["files"] != canonical["files"]):
        raise ValueError("Source world diverges from independently pinned Git tree")
    # Independently resolved through the original upstream git/commits tree
    # pointer and recursive git/trees endpoint. The previous receipt wrongly
    # copied the commit id into the tree field; these are distinct Git objects.
    if (canonical["source_tree_sha1"] !=
            "38bdb12d180303f1738b7c5b6d99f34f157c26f9"
            or tree["source_tree_sha1"] == tree["source_commit"]):
        raise ValueError("Git commit and original tree identities conflated")
    pinned_static = next(
        (x for x in canonical["files"] if x["path"] == "Scripts/StaticGFC.m"),
        None
    )
    if (pinned_static is None or
            sources["pnas_static_script"]["git_blob_sha1"] != pinned_static["git_blob_sha1"]):
        raise ValueError("Original 20-subject namespace not bound to exact author-script Git blob")
    files = tree["files"]
    if len(files) != 56 or len({x["path"] for x in files}) != 56:
        raise ValueError("Expected complete, unique 56-file upstream tree")
    fmri = [x for x in files if re.fullmatch(r"fMRI/LongS[0-9]+(DMT|PCB)[.]mat",
                                            x["path"])]
    if len(fmri) != 40:
        raise ValueError("Expected 20 paired source subjects")
    names = {x["path"].split("/")[1][4:7] for x in fmri}
    if "source_subject_namespace" in artifacts:
        if set(artifacts["source_subject_namespace"]["subject_ids"]) != names:
            raise ValueError("Archived author script IDs disagree with original paired MAT source filenames")
    if len(names) != 20 or any(
        "fMRI/Long%sDMT.mat" % s not in {x["path"] for x in fmri}
        or "fMRI/Long%sPCB.mat" % s not in {x["path"] for x in fmri}
        for s in names
    ):
        raise ValueError("Source repository does not contain 20 complete pairs")
    if any(x["size_bytes"] <= 0 or
           not re.fullmatch(r"[0-9a-f]{40}", x["git_blob_sha1"]) for x in files):
        raise ValueError("Missing exact source Git object IDs")


def claim_status(world: dict) -> list[dict]:
    a = {x["id"]: x for x in world["artifacts"]}
    out = []
    for c in world["claims"]:
        missing = [x for x in c["requires"] if a[x]["status"] != "present"]
        source_scope_absences = [
            x for x in c["requires"] if a[x]["status"] == "knownAbsent"
        ]
        out.append({
            "consumer": c["id"], "grade": c["grade"],
            "required_artifact_ids": c["requires"], "missing": missing,
            "known_absent_in_declared_source_scope": source_scope_absences,
            "state": "source_scope_blocked" if source_scope_absences
                     else ("acquisition_blocked" if missing else (
                         "source_attested_only" if c["grade"] in ("source_claim", "source_metadata")
                         else "requires_independent_validation"
                     )),
        })
    return out


def action_candidates(world: dict) -> list[dict]:
    status = {x["id"]: x["status"] for x in world["artifacts"]}
    # An acquisition cannot rescue a claim whose declared original-tree
    # source requirements are already known absent in that same revision.
    # Such a consumer can be reopened only through a DIFFERENT source-scope
    # claim, not by counting its other prerequisites as live gain.
    unclosed = [c for c in world["claims"]
                if any(status[x] != "present" for x in c["requires"])
                and not any(status[x] == "knownAbsent" for x in c["requires"])]
    out = []
    for action in world["actions"]:
        missing = [x for x in action["needs"] if status[x] != "present"]
        targets = [x for x in action["targets"] if status[x] != "present"]
        affected = [c["id"] for c in unclosed if set(targets) & set(c["requires"])]
        out.append({
            "id": action["id"], "kind": action["kind"],
            "state": "candidate_admissible" if not missing and targets
                     else ("source_prerequisite_blocked" if missing else "defer_no_new_target"),
            "missing_prerequisites": missing, "potential_artifacts": targets,
            "potential_consumer_ids": affected,
            "potential_consumer_count": len(affected),
            "cost_band": action["cost_band"], "access_risk": action["access_risk"],
            "research_action": action["work"],
            "promotion_authorised": False,
        })
    ready = [x for x in out if x["state"] == "candidate_admissible"]
    # Dominance requires coverage of the ACTUAL evidence coordinates as well
    # as consumer labels; targeting the same consumer with a different missing
    # prerequisite does not make either search action redundant.
    for a in out:
        a["pareto"] = a in ready and not any(
            b["id"] != a["id"] and
            b["cost_band"] <= a["cost_band"] and
            b["access_risk"] <= a["access_risk"] and
            set(a["potential_consumer_ids"]) <= set(b["potential_consumer_ids"]) and
            set(a["potential_artifacts"]) <= set(b["potential_artifacts"]) and
            (b["cost_band"] < a["cost_band"] or
             b["access_risk"] < a["access_risk"] or
             set(a["potential_consumer_ids"]) < set(b["potential_consumer_ids"]))
            for b in ready
        )
    return out


def hypothetical_plan(world: dict, claim_id: str) -> dict:
    """Shortest number of successful source bundles conditional on everything working.

    It MUST NOT mutate the world or turn hypothetically obtained artifacts present.
    """
    claims = {x["id"]: x for x in world["claims"]}
    if claim_id not in claims:
        raise ValueError("Unknown consumer")
    needed = frozenset(claims[claim_id]["requires"])
    initial = frozenset(a["id"] for a in world["artifacts"] if a["status"] == "present")
    if needed <= initial:
        return {"consumer": claim_id, "status": "no_acquisition_needed",
                "hypothetical_actions": [], "evidence_created": False}
    candidates = [a for a in world["actions"] if a["targets"] and not any(
        x["status"] == "knownAbsent" and x["id"] in a["needs"]
        for x in world["artifacts"])]
    queue = [(initial, ())]
    seen = {initial}
    while queue:
        state, history = queue.pop(0)
        if needed <= state:
            return {"consumer": claim_id, "status": "conditional_plan_only",
                    "hypothetical_actions": list(history), "evidence_created": False,
                    "source_approval_and_measured_results_still_required": True}
        for act in candidates:
            if not set(act["needs"]) <= state or not set(act["targets"]) - state:
                continue
            newer = state | frozenset(act["targets"])
            if newer not in seen:
                seen.add(newer)
                queue.append((newer, history + (act["id"],)))
    return {"consumer": claim_id, "status": "no_declared_source_route",
            "hypothetical_actions": [], "evidence_created": False}


def candidate_source_receipt(world: dict, artifact_id: str, receipt: dict) -> dict:
    """Preview consumer-specific reopening; NEVER mark the artifact as present.

    A string, hash, URL or asserted custodian signature is not independently
    verified evidence. High-stakes contents and reuse rights need external
    source review; this only describes the consequent consumer obligations.
    """
    validate_world(world)
    artifacts = {a["id"]: a for a in world["artifacts"]}
    if artifact_id not in artifacts:
        raise ValueError("Unknown source artifact coordinate")
    a = artifacts[artifact_id]
    if a["status"] != "notLocated":
        raise ValueError("Only notLocated coordinates accept candidate source tips")
    required = {"source_id", "source_locator", "source_revision",
                "candidate_sha256", "access_scope", "observation_time",
                "verification_method"}
    if not isinstance(receipt, dict) or any(not receipt.get(k) for k in required):
        raise ValueError("Missing provenance or access coordinates")
    if receipt["source_id"] != a["source"]:
        raise ValueError("Proposed source identity differs from required primary root")
    if not re.fullmatch(r"[0-9a-f]{64}", receipt["candidate_sha256"]):
        raise ValueError("Candidate hash must be 64 lower-case SHA256 characters")
    if not receipt["source_locator"].startswith(("https://", "doi:", "git:")):
        raise ValueError("Source locator is not in a supported external namespace")
    consumers = [
        {"consumer": c["id"],
         "remaining_obligations_after_hypothetical_acquisition":
             [x for x in c["requires"] if x != artifact_id and
              artifacts[x]["status"] != "present"],
         "source_evidence_is_sufficient_for_scientific_claim": False}
        for c in world["claims"] if artifact_id in c["requires"]
        and not any(artifacts[x]["status"] == "knownAbsent"
                    for x in c["requires"] if x != artifact_id)
    ]
    excluded_scoped_consumers = [
        c["id"] for c in world["claims"]
        if artifact_id in c["requires"]
        and any(artifacts[x]["status"] == "knownAbsent"
                for x in c["requires"] if x != artifact_id)
    ]
    return {
        "artifact_id": artifact_id,
        "status": "candidate_tip_not_admitted",
        "candidate_provenance": receipt,
        "would_reopen_consumers": consumers,
        "source_scope_blocked_consumers_not_reopened": excluded_scoped_consumers,
        "external_source_rights_and_identity_verified": False,
        "world_mutated": False,
        "artifact_status_after": "notLocated",
    }


def snapshot(world: dict) -> dict:
    return {
        "world_id": world["world_id"],
        "source_records": len(world["sources"]),
        "bibliographic_lineage_roots": len({s["lineage_root"] for s in world["sources"]}),
        "participant_independence_certified": False,
        "source_file_objects": len(world["observed_git_tree"]["files"]),
        "artifact_status_counts": {k: sum(a["status"] == k for a in world["artifacts"])
                                   for k in sorted(STATES)},
        "claims": claim_status(world),
        "action_frontier": action_candidates(world),
        "safety": world["safety"],
        "assertion": "No artifact is acquired, no status is mutated, no rights are granted",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--world", type=Path, default=DEFAULT_WORLD)
    parser.add_argument("--consumer", help="Compute a conditional shortest acquisition route")
    parser.add_argument("--out", type=Path, help="Optional local JSON snapshot file")
    parser.add_argument("--candidate-artifact", help="Preview reopening for one evidence coordinate")
    parser.add_argument("--candidate-receipt", type=Path, help="JSON evidence tip (dry-run only)")
    args = parser.parse_args()
    world = load_world(args.world)
    if bool(args.candidate_artifact) != bool(args.candidate_receipt):
        parser.error("Candidate artifact and candidate receipt must be supplied together")
    if args.candidate_artifact and args.consumer:
        parser.error("Use either a consumer plan or a candidate evidence tip")
    if args.candidate_artifact:
        result = candidate_source_receipt(
            world, args.candidate_artifact,
            json.loads(args.candidate_receipt.read_text(encoding="utf8")))
    else:
        result = hypothetical_plan(world, args.consumer) if args.consumer else snapshot(world)
    rendered = json.dumps(result, indent=2, sort_keys=True)
    if args.out:
        args.out.write_text(rendered + "\n", encoding="utf8")
    else:
        print(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
