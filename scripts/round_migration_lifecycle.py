#!/usr/bin/env python3
"""Build a whole-lifecycle state report for historical Round migration.

This consumes the existing ledger and import plan.  It does not infer theorem
equivalence, rewrite Agda, delete files, or hide failed verification.  Its job
is to keep discovery, repair, mapping, rewrite, verification, rollback, and
deletion states visible in one generated artifact.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from pathlib import Path


def _probe_summary(probe: dict | None) -> dict[str, str]:
    """Summarize receipts by consumer without treating batch passes as authority."""
    summary: dict[str, list[str]] = defaultdict(list)
    if not probe:
        return {}
    receipts = probe.get("receipts", [])
    if "receipt" in probe:
        receipts = [probe["receipt"]]
    for receipt in receipts:
        consumer = receipt.get("consumer")
        if consumer:
            summary[consumer].append(receipt.get("status", "unknown"))
    result = {}
    for consumer, statuses in summary.items():
        result[consumer] = (
            "batch-probe-pass"
            if statuses and all(status == "probe-pass" for status in statuses)
            else "probe-failed-or-incomplete"
        )
    return result


def _candidate_summary(candidates: dict | None) -> dict[str, dict]:
    """Index declaration-candidate evidence by historical module."""
    result: dict[str, dict] = defaultdict(lambda: {
        "status_counts": Counter(),
        "mapping_candidate_count": 0,
        "terminal_mapping_candidate_count": 0,
    })
    if not candidates:
        return {}
    for row in candidates.get("rows", []):
        module = row.get("module")
        if not module:
            continue
        entry = result[module]
        entry["status_counts"][row.get("status", "unknown")] += 1
        if row.get("status") in {"exact-selected-owner", "exact-unique"}:
            entry["mapping_candidate_count"] += 1
            if row.get("target_is_terminal_recipient", False):
                entry["terminal_mapping_candidate_count"] += 1
    return {
        module: {
            "status_counts": dict(sorted(value["status_counts"].items())),
            "mapping_candidate_count": value["mapping_candidate_count"],
            "terminal_mapping_candidate_count": value["terminal_mapping_candidate_count"],
        }
        for module, value in result.items()
    }


def build_lifecycle(ledger: dict, plan: dict, probe: dict | None = None,
                    candidates: dict | None = None) -> dict:
    probe_status = _probe_summary(probe)
    candidate_status = _candidate_summary(candidates)
    rows = []
    for row in plan.get("rows", []):
        status = row["status"]
        if status == "unused-import-remove-or-recheck":
            context_status = probe_status.get(row["consumer"], "not-probed")
            lifecycle = "context-probed-batch-pass" if context_status == "batch-probe-pass" else "repair-needed"
            repair = ("batch probe passed; retain the exact receipt and recheck after the planned "
                      "rewrite" if lifecycle == "context-probed-batch-pass" else
                      "audit Agda-level instance, module, operator, and implicit context before removing this import")
        elif status == "mapping-incomplete":
            lifecycle = "needs-canonical-mapping"
            repair = "attach the already-established canonical declaration mapping"
        elif status == "rewrite-ready":
            lifecycle = "rewrite-ready"
            repair = "run a sanctioned Agda check after the import rewrite"
        else:
            lifecycle = "needs-review"
            repair = "inspect the import/declaration classification"
        rows.append({
            "consumer": row["consumer"],
            "consumer_path": row["consumer_path"],
            "historical_module": row["historical_module"],
            "historical_names_used": row["used_names"],
            "status": status,
            "lifecycle_state": lifecycle,
            "context_probe_status": probe_status.get(row["consumer"], "not-probed"),
            "candidate_evidence": candidate_status.get(row["historical_module"], {
                "status_counts": {},
                "mapping_candidate_count": 0,
                "terminal_mapping_candidate_count": 0,
            }),
            "repair_action": repair,
            "verification_command": (
                "DASHI_NO_TMUX=1 scripts/run_agda29_parallel_check.sh "
                + row["consumer_path"]
            ),
            "rollback_rule": "restore the last verified checkpoint if the consumer fails after rewrite",
        })

    state_counts = Counter(row["lifecycle_state"] for row in rows)
    return {
        "schema_version": 1,
        "purpose": "fail-closed whole-lifecycle Round migration control surface",
        "source_ledger": ".dashi/round-stranded/ym-consolidation-ledger.json",
        "source_plan": ".dashi/round-stranded/ym-migration-plan.json",
        "historical_module_count": ledger.get("historical_module_count", 0),
        "direct_import_edge_count": plan.get("direct_historical_import_edge_count", 0),
        "consumer_count": plan.get("consumer_count", 0),
        "candidate_declaration_count": candidates.get("declaration_count", 0) if candidates else 0,
        "candidate_status_counts": candidates.get("status_counts", {}) if candidates else {},
        "terminal_mapping_candidate_count": candidates.get("terminal_mapping_candidate_count", 0) if candidates else 0,
        "state_counts": dict(sorted(state_counts.items())),
        "gates": [
            {"state": "discovered", "entry": "ledger contains the historical module and importer evidence"},
            {"state": "classified", "entry": "declaration use and reverse-cone role are recorded"},
            {"state": "repair-needed", "entry": "implicit/instance/module/operator context is audited; no blind import removal"},
            {"state": "needs-canonical-mapping", "entry": "historical declarations point to existing non-Round declarations"},
            {"state": "rewrite-ready", "entry": "all used declarations map to one canonical target"},
            {"state": "verified", "entry": "sanctioned Agda check passes after the rewrite"},
            {"state": "rollback", "entry": "failed checks restore the last verified checkpoint and retain the failure receipt"},
            {"state": "deletion-ready", "entry": "zero consumers, no unique declarations, and verified replacement"},
        ],
        "rows": rows,
        "deletion_authorized": False,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ledger", type=Path, default=Path(".dashi/round-stranded/ym-consolidation-ledger.json"))
    parser.add_argument("--plan", type=Path, default=Path(".dashi/round-stranded/ym-migration-plan.json"))
    parser.add_argument("--probe", type=Path, default=None,
                        help="optional context-probe receipt JSON")
    parser.add_argument("--candidates", type=Path, default=None,
                        help="optional declaration-candidate report JSON")
    parser.add_argument("--output", type=Path, default=Path(".dashi/round-stranded/ym-migration-lifecycle.json"))
    args = parser.parse_args()
    lifecycle = build_lifecycle(
        json.loads(args.ledger.read_text(encoding="utf-8")),
        json.loads(args.plan.read_text(encoding="utf-8")),
        json.loads(args.probe.read_text(encoding="utf-8")) if args.probe else None,
        json.loads(args.candidates.read_text(encoding="utf-8")) if args.candidates else None,
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(lifecycle, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({
        "historical_module_count": lifecycle["historical_module_count"],
        "direct_import_edge_count": lifecycle["direct_import_edge_count"],
        "consumer_count": lifecycle["consumer_count"],
        "state_counts": lifecycle["state_counts"],
        "deletion_authorized": lifecycle["deletion_authorized"],
        "output": str(args.output),
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
