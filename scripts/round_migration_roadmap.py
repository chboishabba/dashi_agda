#!/usr/bin/env python3
"""Generate the current YM historical-Round migration roadmap.

The raw ledger intentionally remains fail-closed and therefore has larger
counts than the semantic migration queue.  This report keeps those views
separate and records the gates needed before deletion is allowed.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def build_roadmap(ledger: dict, plan: dict, candidates: dict, bundles: dict,
                  reconciliation: dict | None = None) -> dict:
    relevance = candidates.get("migration_relevance_counts", {})
    live_declaration_count = relevance.get("live-declaration-use", 0)
    source_bundles = bundles.get("bundle_count", 0)
    source_declarations = bundles.get("declaration_count", 0)
    structural_bundles = bundles.get("shared_structural_bundle_count", 0)
    structural_declarations = bundles.get("shared_structural_declaration_count", 0)
    live_candidate_rows = [
        row for row in candidates.get("rows", [])
        if row.get("migration_relevance") == "live-declaration-use"
    ]
    source_bearing_keys = {
        (bundle.get("historical_module"), declaration.get("name"))
        for bundle in bundles.get("bundles", [])
        for declaration in bundle.get("declarations", [])
    }
    source_bearing_live_candidates = [
        row for row in live_candidate_rows
        if (row.get("module"), row.get("name")) in source_bearing_keys
    ]
    mapping_incomplete_rows = [
        row for row in plan.get("rows", [])
        if row.get("status") == "mapping-incomplete"
    ]
    mapping_incomplete_declarations = {
        (row.get("historical_module"), name)
        for row in mapping_incomplete_rows
        for name in row.get("used_names", [])
    }
    recipient_review_bundles = [
        bundle for bundle in bundles.get("bundles", [])
        if bundle.get("recipient_status") == "recipient-review-required"
    ]
    structural_review_bundles = [
        bundle for bundle in bundles.get("shared_structural_bundles", [])
        if bundle.get("recipient_status") in {
            "recipient-review-required",
            "status-owner-review-required",
        }
    ]
    live_historical_modules = sum(
        bool(row.get("reverse_cone_nonhistorical_consumers"))
        for row in ledger.get("modules", [])
    )
    proof_item_ids = {
        "walsh-spectral-identity",
        "trace-p2-safe-boundary",
        "cmp98-pointwise-repair-cone-v20",
        "cmp98-pointwise-repair-cone-v53",
    }
    completed = []
    for item in _completed_items():
        item = dict(item)
        item["scope"] = "proof-cone-external" if item["id"] in proof_item_ids else "historical-round-migration"
        item["blocking_for_migration"] = item["scope"] == "historical-round-migration"
        completed.append(item)
    reconciliation_queue_counts = (reconciliation or {}).get("queue_counts", {})
    external_count = sum(item["scope"] == "proof-cone-external" for item in completed)
    return {
        "schema_version": 1,
        "purpose": "YM historical Round to canonical Clay migration roadmap",
        "generated_from": {
            "ledger": ".dashi/round-stranded/ym-consolidation-ledger.json",
            "migration_plan": ".dashi/round-stranded/ym-migration-plan.json",
            "candidates": ".dashi/round-stranded/ym-migration-candidates.json",
            "live_bundle_plan": ".dashi/round-stranded/ym-live-bundle-plan.json",
        },
        "interpretation": {
            "historical_files_on_disk_are_not_outstanding_proofs": True,
            "ledger_states_are_fail_closed_bookkeeping": True,
            "semantic_queue_is_live_declarations_and_bundles": True,
        },
        "current_snapshot": {
            "historical_files_on_disk": ledger.get("historical_module_count", 0),
            "historical_modules_with_live_consumers": live_historical_modules,
            "live_consumers": plan.get("consumer_count", 0),
            "direct_historical_import_edges": plan.get("direct_historical_import_edge_count", 0),
            "current_source_plan_is_fresh": True,
            "ledger_mapping_incomplete_rows": plan.get("status_counts", {}).get("mapping-incomplete", 0),
            "ledger_context_repair_rows": plan.get("status_counts", {}).get("unused-import-remove-or-recheck", 0),
            "live_declaration_uses": live_declaration_count,
            "live_module_context_cases": relevance.get("live-module-context", 0),
            "no_live_consumer_cases": relevance.get("no-live-consumer", 0),
            "source_bundles": source_bundles,
            "source_bearing_declarations": source_declarations,
            "shared_structural_bundles": structural_bundles,
            "shared_structural_declarations": structural_declarations,
            "mapping_incomplete_import_edges": len(mapping_incomplete_rows),
            "mapping_incomplete_unique_declarations": len(mapping_incomplete_declarations),
            "candidate_live_declaration_uses": len(live_candidate_rows),
            "candidate_source_bearing_live_declarations": len(source_bearing_live_candidates),
            "candidate_metadata_live_declarations": len(live_candidate_rows) - len(source_bearing_live_candidates),
            "recipient_review_bundles": len(recipient_review_bundles) + len(structural_review_bundles),
            "reconciliation_action_counts": (reconciliation or {}).get("action_counts", {}),
            "reconciliation_declaration_action_counts": (reconciliation or {}).get("declaration_action_counts", {}),
            "reconciliation_unique_declaration_action_counts": (reconciliation or {}).get("unique_declaration_action_counts", {}),
            "migration_queue_counts": reconciliation_queue_counts,
            "bookkeeping_context_rows": reconciliation_queue_counts.get("bookkeeping-context", 0),
            "external_proof_cone_item_count": external_count,
            "deletion_authorized": False,
        },
        "completed_or_attempted": completed,
        "remaining_steps": [
            {
                "id": "external-proof-cones",
                "status": "nonblocking",
                "scope": "canonical YM/NS proof obligations encountered while checking migration consumers",
                "action": "retain receipts and resolve independently; do not count these as historical-R migration rows",
            },
            {
                "id": "extract-four-live-bundles",
                "status": "semantic-actions-complete-verification-blocked",
                "scope": f"{source_bundles} bundles / {source_declarations} source-bearing declarations; semantic actions complete, verification/deletion gates remain",
                "action": "finish consumer rewiring and close the verification/deletion gates for the extracted bundles",
                "evidence": ".dashi/round-stranded/ym-live-bundle-plan.json",
            },
            {
                "id": "resolve-shared-structural-bundles",
                "status": "recipient-review-required",
                "scope": f"{structural_bundles} shared structural bundles / {structural_declarations} declarations; includes the three former semantic-mapping rows",
                "action": "select an existing non-Round owner only after import-cycle and dependent-projection analysis; preserve status surfaces without theorem remapping",
                "evidence": ".dashi/round-stranded/ym-live-bundle-plan.json",
            },
            {
                "id": "rewire-live-consumers",
                "status": "semantic-actions-complete-verification-blocked",
                "scope": "live consumers of historical declarations and imports",
                "action": "replace historical references and imports while preserving local type/import closure",
                "evidence": ".dashi/round-stranded/ym-migration-plan.json",
            },
            {
                "id": "verify-affected-cones",
                "status": "migration-gated-by-linked-cones",
                "scope": "each repaired historical consumer cone",
                "action": "run the sanctioned Agda entrypoint and retain receipts; classify unrelated canonical failures as external",
                "command": "DASHI_NO_TMUX=1 scripts/run_agda29_parallel_check.sh <target>",
            },
            {
                "id": "reclassify-context-cases",
                "status": "automatable",
                "scope": f"{relevance.get('live-module-context', 0)} module-context cases",
                "action": "rescan implicit, instance, module, and operator dependencies; remove only verified unused imports",
                "evidence": ".dashi/round-stranded/ym-context-audit.json",
            },
            {
                "id": "reconcile-generated-actions",
                "status": "complete" if reconciliation else "pending",
                "scope": "all migration-plan and context-audit rows",
                "action": "consume the existing JSON reports and separate migration-ready, mechanical-repair, and external proof-cone queues",
                "evidence": ".dashi/round-stranded/ym-migration-reconciliation.json",
            },
            {
                "id": "open-deletion-gates",
                "status": "automatable-after-rewiring",
                "scope": f"{relevance.get('no-live-consumer', 0)} no-live-consumer cases",
                "action": "confirm zero current source importers, zero reverse consumers, and verified replacement before deletion",
                "evidence": ".dashi/round-stranded/ym-migration-plan.json plus a fresh source scan",
            },
        ],
        "deletion_gate": {
            "authorized": False,
            "requirements": [
                "all direct and reverse-cone consumers rewired",
                "sanctioned Agda verification passes after rewrites",
                "zero remaining importers of each candidate historical file",
                "no unique declaration or required module context remains",
                "checkpoint and rollback receipt recorded",
            ],
        },
    }


def _completed_items() -> list[dict]:
    return [
            {
                "id": "r275-ursell-compiler-extraction",
                "status": "rewired-verification-blocked",
                "action": "Removed all nonhistorical Agda imports of R275; moved the Ursell compiler dependency into the canonical donor and rewired R282/R286 directly through Gap.",
                "target": "BalabanClayCanonicalBUrsellDonorBidiExact, BalabanClayCanonicalBFrontierRound282Exact, BalabanDirectCanonicalBCompletionRound286Exact",
                "verification": "sanctioned Agda check reached the dependency cone but was blocked by an existing unsafe import in the shared introspection/Ursell chain",
                "next_action": "repair or adjudicate the pre-existing safe-import boundary, then rerun affected-cone checks before deleting R275",
            },
            {
                "id": "r330-route-s-and-direct-source-rewire",
                "status": "rewired-verification-blocked",
                "action": "Moved the R330 order-closure compatibility adapter into the existing Route-S canonical file and inlined the zero-fresh-B status coordinate into the direct-source frontier; removed nonhistorical R330 imports.",
                "target": "YMClayRouteSSelectedLimitClosureExact, BalabanCanonicalBOSIndexedCompletionRound333Exact, YMClayDirectSourceOSMassGapFrontierExact",
                "verification": "walshSpectralIdentityRaw is constructive, the Boolean/trace/P2 safe boundary checks, and the Route-S target now reaches the intentional DASHI.Foundations.RealAnalysisAxioms postulate boundary",
                "next_action": "keep the real-analysis authority explicit; rerun the affected cone only after a separately reviewed replacement or adjudication of that authority boundary",
            },
            {
                "id": "walsh-spectral-identity",
                "status": "constructively-verified",
                "action": "Replace walshSpectralIdentityRaw with the finite 16-variable rational-ring certificate and mark the module safe.",
                "target": "BalabanBoolean4BlockPoincareExact",
                "verification": "sanctioned Colab Agda check passed for the module; the downstream safe cone now proceeds past it and stops at the pre-existing P2 unsafe import",
                "next_action": "retain the proof receipt and continue safe-boundary repair at BalabanClayP2LargeFieldStepVExact",
            },
            {
                "id": "trace-p2-safe-boundary",
                "status": "constructively-verified",
                "action": "Mark the postulate-free geometric trace and finite P2 certificate surfaces safe without promoting their conditional physical producer fields.",
                "target": "BalabanTraceKoteckyPreissGeometricExact, BalabanClayP2LargeFieldStepVExact",
                "verification": "sanctioned Colab Agda check passed through BalabanClayT2TraversalRootedShellExact",
                "next_action": "retain the explicit conditional ProofLevel fields and continue at the real-analysis authority boundary",
            },
            {
                "id": "r77-h6-bundle-extraction",
                "status": "rewired-verification-blocked",
                "action": "Reproduced the Round77 same-H Gaussian/Ward compiler bundle in the canonical H6 recipient and removed H6's direct R77 import.",
                "target": "YangMillsDirectSourceOSSameSystemH6Exact",
                "verification": "Colab receipt /content/ym-r77-h6-repair-20261128.log: the moved bundle parses, then the sanctioned H6 check stops at the pre-existing unsafe YangMillsClayLiteralTopDownConstructionExact import in the safe cone",
                "next_action": "keep the authority boundary explicit, then rewire the remaining historical R77 wrappers and verify the H6 cone after that boundary is separately reviewed",
            },
            {
                "id": "r78-route-s-bundle-extraction",
                "status": "rewired-verification-blocked",
                "action": "Reproduced the Round78 top-down endpoint records and compiler in the canonical Route-S recipient and removed Route-S's direct R78 import.",
                "target": "YMClayLiteralTopDownRouteSClosureExact",
                "verification": "Colab receipt /content/ym-r78-pinned-route-repair-20261128-v2.log: the moved bundle parses, then the sanctioned Route-S cone reaches the pre-existing unsafe YangMillsClayProblemContractExact authority boundary",
                "next_action": "rewire remaining historical R78 wrappers, then rerun the affected Route-S cone after the authority boundary is separately reviewed",
            },
            {
                "id": "r270-r87-wrapper-rewire",
                "status": "rewired-verification-blocked",
                "action": "Rewired the R270 mass-gap consumer to the canonical Route-S owner and removed the unused R77 import from the R87 analytic wrapper; no historical R77/R78 import remains in either file.",
                "target": "BalabanClayCanonicalMassGapConsumerRound270Exact, BalabanClayHighestAlphaRound87FourAnalyticLemmaExact",
                "verification": "current-source migration scan reports neither wrapper as a direct historical importer; R270 Colab receipt /content/ym-r270-wrapper-rewire-20261128-v2.log reaches the pre-existing unsafe IntrospectiveProofLoopExact boundary, while R87 reaches the pre-existing parser failure in BalabanTopDownSummableRGIncrementExact",
                "next_action": "keep both authority/parser boundaries explicit, then continue with the next script-ranked historical wrappers",
            },
            {
                "id": "r77-historical-wrapper-rewire",
                "status": "rewired-verification-blocked",
                "action": "Rewired the remaining historical R468 and R439 bridge wrappers from the R77 source module to the canonical H6 recipient and exposed the preserved bridge-level status there.",
                "target": "YangMillsClayGoal1NontrivialityAttachmentRound468Exact, YangMillsClayGoal1SameHNontrivialityRound439Exact, YangMillsDirectSourceOSSameSystemH6Exact",
                "verification": "bounded sanctioned local checks reached pre-existing boundaries: /home/c/.gemini/antigravity/scratch/dashi-agda29-parallel-check-20261128-202856-DASHI__Physics__YangMills__YangMillsClayGoal1NontrivialityAttachmentRound468Exact.agda.log stops at BalabanOSMassGapClosure parser syntax, and /home/c/.gemini/antigravity/scratch/dashi-agda29-parallel-check-20261128-202915-DASHI__Physics__YangMills__YangMillsClayGoal1SameHNontrivialityRound439Exact.agda.log stops at the unsafe TopDownConstruction import",
                "next_action": "repair or separately adjudicate those pre-existing boundaries before opening the R77 deletion gate",
            },
            {
                "id": "cmp98-pointwise-repair-cone-v20",
                "status": "constructively-verified",
                "action": "Repaired the CMP98 pointwise source cone: record-field qualification, lambda parsing, explicit recursive parameters, unequal-term construction, and false safe-boundary declarations were corrected without changing theorem statements.",
                "target": "BalabanCMP98Equation119ExistingPrincipalLogRound156Exact and its transitive CMP98 pointwise cone",
                "verification": "sanctioned Colab Agda 2.9.0 check on worker dashi-agda-worker-2 passed; only the pre-existing PatternShadowsConstructor warning remains (receipt: .dashi/round-stranded/ym-repair-pointwise-worker2-v20-20261129.log)",
                "next_action": "use this clean cone as the baseline for the next script-ranked historical consumer; do not reopen these repairs unless a downstream check identifies a new dependency failure",
            },
            {
                "id": "cmp98-pointwise-repair-cone-v53",
                "status": "in-progress-colab-check",
                "action": "Repair the next transitive CMP98/P33 pointwise cone failures found by the worker-2 Agda probe: false safe declarations, record-field parsing, rational/list imports, recursive Nat addition transport, and total-remainder equality orientation.",
                "target": "BalabanCMP98Equation119PointwiseSemanticSelectedCutExact and the R170/R168/R164/P33 dependencies it exposes",
                "verification": "worker-2 receipt /content/ym-repair-pointwise-worker2-v53-20261129.log is actively checking after the latest repairs; no clean result recorded yet",
                "next_action": "let the existing worker-2 job finish, download its wrapper receipt, then classify the next failure or promote the cone only on a clean result",
            },
        ]


def markdown(report: dict) -> str:
    snap = report["current_snapshot"]
    lines = [
        "# YM historical Round migration roadmap",
        "",
        "> Generated by `scripts/round_migration_roadmap.py`. This is a migration control surface, not proof authority.",
        "",
        "## Current position",
        "",
        "The historical-file count is a filesystem/reachability count, not a count of missing proofs. The semantic queue is the live declaration and bundle count.",
        "",
        f"- Historical files on disk: **{snap['historical_files_on_disk']}**",
        f"- Live consumers: **{snap['live_consumers']}**",
        f"- Candidate live declaration uses: **{snap['candidate_live_declaration_uses']}**",
        f"- Of those, source-bearing: **{snap['candidate_source_bearing_live_declarations']}**; metadata/status: **{snap['candidate_metadata_live_declarations']}**",
        f"- Mapping-incomplete import edges: **{snap['mapping_incomplete_import_edges']}**, covering **{snap['mapping_incomplete_unique_declarations']}** unique declaration names",
        f"- Live module-context cases: **{snap['live_module_context_cases']}**",
        f"- No-live-consumer cases: **{snap['no_live_consumer_cases']}**",
        f"- Source bundles tracked: **{snap['source_bundles']}** (semantic recipient decisions complete)",
        f"- Source-bearing declarations in those bundles: **{snap['source_bearing_declarations']}**",
        f"- Bundles still needing recipient review: **{snap['recipient_review_bundles']}**",
        f"- Reconciliation actions: **{snap['reconciliation_action_counts']}**",
        f"- Reconciliation declaration actions: **{snap['reconciliation_declaration_action_counts']}**",
        f"- Reconciliation unique declaration actions: **{snap['reconciliation_unique_declaration_action_counts']}**",
        f"- Migration queues: **{snap['migration_queue_counts']}**",
        f"- External proof-cone items (nonblocking): **{snap['external_proof_cone_item_count']}**",
        "- Deletion authorized: **false**",
        "",
    ]
    lines += [
        "",
        "## Completed or attempted",
        "",
        "| Item | Status | Result |",
        "|---|---|---|",
    ]
    for item in report["completed_or_attempted"]:
        lines.append(f"| `{item['id']}` | **{item['status']}** | {item['verification']} |")
    lines += [
        "",
        "## Remaining steps",
        "",
        "| Step | Status | Action |",
        "|---|---|---|",
    ]
    for step in report["remaining_steps"]:
        lines.append(f"| `{step['id']}` | **{step['status']}** | {step['action']} |")
    lines += [
        "",
        "## Deletion gate",
        "",
        "A historical file is removable only after every current source consumer is rewired, the sanctioned Agda check passes, a fresh import/reverse-consumer scan finds nothing remaining, and the rollback/checkpoint receipt is recorded. The package ledger is evidence, but the regenerated current-source migration plan controls deletion decisions while package data is stale.",
        "",
        "Machine-readable state: `.dashi/round-stranded/ym-migration-roadmap.json`.",
        "",
    ]
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path("."))
    parser.add_argument("--output", type=Path, default=Path(".dashi/round-stranded/ym-migration-roadmap.json"))
    parser.add_argument("--markdown-output", type=Path, default=Path("Docs/physics/YMClayHistoricalRoundMigrationRoadmap20261128.md"))
    parser.add_argument("--reconciliation", type=Path, default=Path(".dashi/round-stranded/ym-migration-reconciliation.json"))
    args = parser.parse_args()
    root = args.repo_root.resolve()
    base = root / ".dashi/round-stranded"
    report = build_roadmap(
        json.loads((base / "ym-consolidation-ledger.json").read_text()),
        json.loads((base / "ym-migration-plan.json").read_text()),
        json.loads((base / "ym-migration-candidates.json").read_text()),
        json.loads((base / "ym-live-bundle-plan.json").read_text()),
        json.loads((root / args.reconciliation).read_text()) if (root / args.reconciliation).is_file() else None,
    )
    output = root / args.output
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    markdown_output = root / args.markdown_output
    markdown_output.parent.mkdir(parents=True, exist_ok=True)
    markdown_output.write_text(markdown(report))
    print(json.dumps({
        "source_bundles": report["current_snapshot"]["source_bundles"],
        "source_bearing_declarations": report["current_snapshot"]["source_bearing_declarations"],
        "deletion_authorized": report["current_snapshot"]["deletion_authorized"],
        "output": str(output),
        "markdown_output": str(markdown_output),
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
