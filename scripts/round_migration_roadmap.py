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


def build_roadmap(ledger: dict, plan: dict, candidates: dict, bundles: dict) -> dict:
    relevance = candidates.get("migration_relevance_counts", {})
    live_declaration_count = relevance.get("live-declaration-use", 0)
    source_bundles = bundles.get("bundle_count", 0)
    source_declarations = bundles.get("declaration_count", 0)
    live_historical_modules = sum(
        bool(row.get("reverse_cone_nonhistorical_consumers"))
        for row in ledger.get("modules", [])
    )
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
            "ledger_mapping_incomplete_rows": plan.get("status_counts", {}).get("mapping-incomplete", 0),
            "ledger_context_repair_rows": plan.get("status_counts", {}).get("unused-import-remove-or-recheck", 0),
            "live_declaration_uses": live_declaration_count,
            "live_module_context_cases": relevance.get("live-module-context", 0),
            "no_live_consumer_cases": relevance.get("no-live-consumer", 0),
            "source_bundles": source_bundles,
            "source_bearing_declarations": source_declarations,
            "deletion_authorized": False,
        },
        "completed_or_attempted": [
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
                "verification": "walshSpectralIdentityRaw is now a constructive finite rational-ring certificate and the Boolean block module checks; the downstream cone reaches a separate pre-existing unsafe import at BalabanClayP2LargeFieldStepVExact",
                "next_action": "repair or adjudicate the P2 safe-import boundary, then rerun the affected cone before deleting R330",
            },
            {
                "id": "walsh-spectral-identity",
                "status": "constructively-verified",
                "action": "Replace walshSpectralIdentityRaw with the finite 16-variable rational-ring certificate and mark the module safe.",
                "target": "BalabanBoolean4BlockPoincareExact",
                "verification": "sanctioned Colab Agda check passed for the module; the downstream safe cone now proceeds past it and stops at the pre-existing P2 unsafe import",
                "next_action": "retain the proof receipt and continue safe-boundary repair at BalabanClayP2LargeFieldStepVExact",
            },
        ],
        "remaining_steps": [
            {
                "id": "extract-four-live-bundles",
                "status": "ready-for-repair",
                "scope": f"{source_bundles} bundles / {source_declarations} source-bearing declarations",
                "action": "inline or reproduce each bundle in its existing semantic Clay recipient",
                "evidence": ".dashi/round-stranded/ym-live-bundle-plan.json",
            },
            {
                "id": "rewire-live-consumers",
                "status": "blocked-on-bundle-repair",
                "scope": "live consumers of historical declarations and imports",
                "action": "replace historical references and imports while preserving local type/import closure",
                "evidence": ".dashi/round-stranded/ym-migration-plan.json",
            },
            {
                "id": "verify-affected-cones",
                "status": "blocked-on-existing-unsafe-p2",
                "scope": "each repaired consumer cone",
                "action": "run the sanctioned Agda entrypoint and retain receipts",
                "command": "DASHI_NO_TMUX=1 scripts/run_agda29_parallel_check.sh <target>",
            },
            {
                "id": "reclassify-context-cases",
                "status": "automatable-after-rewiring",
                "scope": f"{relevance.get('live-module-context', 0)} module-context cases",
                "action": "rescan implicit, instance, module, and operator dependencies; remove only verified unused imports",
                "evidence": ".dashi/round-stranded/ym-context-audit.json",
            },
            {
                "id": "open-deletion-gates",
                "status": "automatable-after-rewiring",
                "scope": f"{relevance.get('no-live-consumer', 0)} no-live-consumer cases",
                "action": "confirm zero importers, zero reverse consumers, and verified replacement before deletion",
                "evidence": ".dashi/round-stranded/ym-consolidation-ledger.json",
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
        f"- Live declaration uses: **{snap['live_declaration_uses']}**",
        f"- Live module-context cases: **{snap['live_module_context_cases']}**",
        f"- No-live-consumer cases: **{snap['no_live_consumer_cases']}**",
        f"- Source bundles requiring semantic migration: **{snap['source_bundles']}**",
        f"- Source-bearing declarations in those bundles: **{snap['source_bearing_declarations']}**",
        "- Deletion authorized: **false**",
        "",
        "## Remaining steps",
        "",
        "| Step | Status | Action |",
        "|---|---|---|",
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
    ]
    for step in report["remaining_steps"]:
        lines.append(f"| `{step['id']}` | **{step['status']}** | {step['action']} |")
    lines += [
        "",
        "## Deletion gate",
        "",
        "A historical file is removable only after every consumer is rewired, the sanctioned Agda check passes, a fresh import/reverse-consumer scan finds nothing remaining, and the rollback/checkpoint receipt is recorded. The raw ledger may remain fail-closed while these gates are being satisfied.",
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
    args = parser.parse_args()
    root = args.repo_root.resolve()
    base = root / ".dashi/round-stranded"
    report = build_roadmap(
        json.loads((base / "ym-consolidation-ledger.json").read_text()),
        json.loads((base / "ym-migration-plan.json").read_text()),
        json.loads((base / "ym-migration-candidates.json").read_text()),
        json.loads((base / "ym-live-bundle-plan.json").read_text()),
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
