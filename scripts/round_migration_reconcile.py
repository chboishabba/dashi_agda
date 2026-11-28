#!/usr/bin/env python3
"""Reconcile the generated YM Round migration reports into executable actions.

The migration plan counts import edges, while the candidate and bundle reports
count declarations.  This tool joins those surfaces so the lifecycle does not
present every edge as a missing theorem mapping.  It never invents a canonical
owner: only an explicit bundle recipient or an existing candidate classification
is used, and generic signature evidence remains unresolved.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any


def _read(path: Path, default: dict[str, Any] | None = None) -> dict[str, Any]:
    if not path.is_file():
        return default or {}
    return json.loads(path.read_text(encoding="utf-8"))


def _bundle_index(bundles: dict[str, Any]) -> dict[tuple[str, str], dict[str, Any]]:
    result = {}
    for bundle in bundles.get("bundles", []):
        for declaration in bundle.get("declarations", []):
            result[(bundle.get("historical_module", ""), declaration.get("name", ""))] = {
                "class": "confirmed-bundle-migration",
                "bundle": bundle.get("historical_module"),
                "recipient": bundle.get("proposed_recipient") or bundle.get("semantic_recipients", [None])[0],
                "migration_action": declaration.get("migration_action"),
            }
    return result


def _candidate_index(candidates: dict[str, Any]) -> dict[tuple[str, str], dict[str, Any]]:
    return {
        (row.get("module", ""), row.get("name", "")): row
        for row in candidates.get("rows", [])
    }


def _source_kind_index(repo_root: Path, ledger: dict[str, Any]) -> dict[tuple[str, str], str]:
    """Detect status surfaces and shared record interfaces from source text.

    This is deliberately structural rather than name-similarity based: a
    ProofLevel declaration is metadata, while a record imported by several
    live consumers is a bundle/interface migration.  Neither is a theorem
    identity mapping.
    """
    result: dict[tuple[str, str], str] = {}
    for module in ledger.get("modules", []):
        path = repo_root / module.get("path", "")
        if not path.is_file():
            continue
        text = path.read_text(encoding="utf-8")
        names = set(re.findall(r"^\s*record\s+([A-Za-z][A-Za-z0-9_]*)", text, re.MULTILINE))
        names.update(re.findall(r"^\s*([A-Za-z][A-Za-z0-9_]*)\s*:\s*ProofLevel\b", text, re.MULTILINE))
        for name in names:
            if re.search(rf"^\s*{re.escape(name)}\s*:\s*ProofLevel\b", text, re.MULTILINE):
                result[(module.get("module", ""), name)] = "metadata-status-use"
            elif re.search(rf"^\s*record\s+{re.escape(name)}\b", text, re.MULTILINE):
                result[(module.get("module", ""), name)] = "shared-structural-bundle"
    return result


def _probe_index(probe: dict[str, Any]) -> dict[tuple[str, str, int], list[dict[str, Any]]]:
    result: dict[tuple[str, str, int], list[dict[str, Any]]] = defaultdict(list)
    receipts = probe.get("receipts", [])
    if "receipt" in probe:
        receipts = [probe["receipt"]]
    for receipt in receipts:
        consumer = receipt.get("consumer", "")
        path = receipt.get("consumer_path", "")
        for item in receipt.get("removed_imports", []):
            result[(consumer, item.get("historical_module", ""), item.get("line", -1))].append(receipt)
        # Older receipts remain useful as consumer-level evidence but cannot
        # authorize a source edit without exact import line/hash data.
        if not receipt.get("removed_imports"):
            result[(consumer, path, -1)].append(receipt)
    return result


def _source_hash(repo_root: Path, relative_path: str) -> str | None:
    path = repo_root / relative_path
    if not path.is_file():
        return None
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _queue_for_action(action: str) -> tuple[str, bool]:
    """Return the control queue and whether the row blocks migration.

    Every row originating in the historical import plan is migration scope.
    The distinction is between ready-to-apply evidence and work still needed;
    proof-cone work is never inferred from a large declaration count here.
    """
    if action == "probe-removable-batch":
        return "migration-ready", True
    if action in {"confirmed-bundle-migration", "metadata-status-use", "semantic-action-confirmed"}:
        return "migration", True
    if action == "context-probe-required":
        return "mechanical-repair", True
    if action == "bookkeeping-context":
        # The migration plan retains these edges for auditability, but the
        # candidate report has already established that they do not name a
        # live declaration.  They are not probe work and do not block
        # migration.
        return "bookkeeping-context", False
    return "migration", True


def build_reconciliation(
    repo_root: Path,
    ledger: dict[str, Any],
    plan: dict[str, Any],
    candidates: dict[str, Any],
    bundles: dict[str, Any],
    audit: dict[str, Any],
    probe: dict[str, Any] | None = None,
) -> dict[str, Any]:
    bundle_index = _bundle_index(bundles)
    candidate_index = _candidate_index(candidates)
    source_kind_index = _source_kind_index(repo_root, ledger)
    historical_modules = {
        module.get("module", "") for module in ledger.get("modules", [])
    }
    probe_index = _probe_index(probe or {})
    audit_keys = {
        (row.get("consumer", ""), row.get("historical_module", ""), row.get("line", -1))
        for row in audit.get("rows", [])
    }
    rows = []
    for source_row in plan.get("rows", []):
        consumer = source_row.get("consumer", "")
        module = source_row.get("historical_module", "")
        used_names = source_row.get("used_names", [])
        declaration_actions = []
        for name in used_names:
            key = (module, name)
            if key in bundle_index:
                declaration_actions.append({"name": name, **bundle_index[key]})
                continue
            source_kind = source_kind_index.get(key)
            if source_kind:
                declaration_actions.append({
                    "name": name,
                    "class": source_kind,
                    "migration_action": (
                        "preserve-status-surface"
                        if source_kind == "metadata-status-use"
                        else "extract-shared-record-bundle"
                    ),
                })
                continue
            candidate = candidate_index.get(key)
            if candidate and candidate.get("migration_relevance") == "live-declaration-use":
                # The six non-bundle live uses are routing/status surfaces in
                # the established report, not safe theorem-identity mappings.
                declaration_actions.append({
                    "name": name,
                    "class": "metadata-status-use",
                    "candidate_status": candidate.get("status"),
                })
                continue
            declaration_actions.append({
                "name": name,
                "class": "unresolved-semantic-mapping",
                "candidate_status": candidate.get("status") if candidate else None,
            })

        key = (consumer, module, source_row.get("line", -1))
        receipts = probe_index.get(key, [])
        passing = [receipt for receipt in receipts if receipt.get("status") == "probe-pass"]
        if passing:
            action = "probe-removable-batch"
        elif (
            source_row.get("status") == "mapping-incomplete"
            and module in historical_modules
            and any(item["class"] == "unresolved-semantic-mapping" for item in declaration_actions)
            and all(candidate_index.get((module, name)) is None for name in used_names)
        ):
            # The candidate report has already shown that this historical
            # import edge has no live declaration candidate.  Keep it in the
            # audit ledger, but do not turn it into a probe or mapping task.
            action = "bookkeeping-context"
        elif declaration_actions and not any(
            item["class"] == "unresolved-semantic-mapping"
            for item in declaration_actions
        ) and all(item["class"] == "metadata-status-use" for item in declaration_actions):
            action = "metadata-status-use"
        elif declaration_actions and not any(
            item["class"] == "unresolved-semantic-mapping"
            for item in declaration_actions
        ) and any(item["class"] == "shared-structural-bundle" for item in declaration_actions):
            action = "shared-bundle-migration"
        elif declaration_actions and not any(
            item["class"] == "unresolved-semantic-mapping"
            for item in declaration_actions
        ) and any(item["class"] == "confirmed-bundle-migration" for item in declaration_actions):
            action = "semantic-action-confirmed"
        elif key in audit_keys and not receipts:
            # Every import edge is probed before it is promoted to a semantic
            # mapping gap.  This catches redundant re-exports and context-only
            # imports that textual name analysis cannot see.
            action = "context-probe-required"
        elif source_row.get("status") == "unused-import-remove-or-recheck":
            action = "context-probe-required"
        elif any(item["class"] == "unresolved-semantic-mapping" for item in declaration_actions):
            # The package/import plan calls these mapping-incomplete because
            # it sees a historical import edge, but the candidate report has
            # no declaration candidate for them.  For historical modules this
            # is the already-known module-context/bookkeeping population, not
            # a semantic mapping queue and not an Agda probe queue.
            action = "unresolved-semantic-mapping"
        elif declaration_actions and all(
            item["class"] == "metadata-status-use" for item in declaration_actions
        ):
            action = "metadata-status-use"
        elif any(item["class"] == "shared-structural-bundle" for item in declaration_actions):
            action = "shared-bundle-migration"
        elif declaration_actions:
            action = "semantic-action-confirmed"
        else:
            action = "context-probe-required"
        queue, blocking = _queue_for_action(action)
        rows.append({
            "consumer": consumer,
            "consumer_path": source_row.get("consumer_path"),
            "line": source_row.get("line"),
            "historical_module": module,
            "plan_status": source_row.get("status"),
            "used_names": used_names,
            "declaration_actions": declaration_actions,
            "action": action,
            "scope": "historical-round-migration",
            "queue": queue,
            "blocking_for_migration": blocking,
            "probe_receipt_count": len(receipts),
            "passing_probe_receipt_count": len(passing),
            "source_sha256": _source_hash(repo_root, source_row.get("consumer_path", "")),
            "in_context_audit": key in audit_keys,
        })

    # Preserve audit rows that did not have a direct plan row, so the generated
    # report is a complete action surface rather than a partial join.
    known = {(row["consumer"], row["historical_module"], row["line"]) for row in rows}
    for audit_row in audit.get("rows", []):
        key = (audit_row.get("consumer", ""), audit_row.get("historical_module", ""), audit_row.get("line", -1))
        if key in known:
            continue
        receipts = probe_index.get(key, [])
        action = "probe-removable-batch" if any(r.get("status") == "probe-pass" for r in receipts) else "context-probe-required"
        queue, blocking = _queue_for_action(action)
        rows.append({
            "consumer": audit_row.get("consumer"),
            "consumer_path": audit_row.get("consumer_path"),
            "line": audit_row.get("line"),
            "historical_module": audit_row.get("historical_module"),
            "plan_status": "context-audit-only",
            "used_names": [],
            "declaration_actions": [],
            "action": action,
            "scope": "historical-round-migration",
            "queue": queue,
            "blocking_for_migration": blocking,
            "probe_receipt_count": len(receipts),
            "passing_probe_receipt_count": sum(r.get("status") == "probe-pass" for r in receipts),
            "source_sha256": _source_hash(repo_root, audit_row.get("consumer_path", "")),
            "in_context_audit": True,
        })

    action_counts = Counter(row["action"] for row in rows)
    queue_counts = Counter(row["queue"] for row in rows)
    # Keep the third lifecycle queue explicit even when no proof-cone receipt
    # has been attached yet.  Canonical proof work is ingested separately and
    # must never disappear merely because this report has no such rows.
    queue_counts.setdefault("migration-ready", 0)
    queue_counts.setdefault("mechanical-repair", 0)
    queue_counts.setdefault("proof-cone-external", 0)
    declaration_counts = Counter(
        item["class"]
        for row in rows
        for item in row["declaration_actions"]
    )
    unique_declaration_counts = Counter()
    seen_declarations = set()
    for row in rows:
        for item in row["declaration_actions"]:
            key = (row["historical_module"], item.get("name"), item.get("class"))
            if key not in seen_declarations:
                seen_declarations.add(key)
                unique_declaration_counts[item["class"]] += 1
    known_bundle_count = len(bundle_index)
    known_live_candidate_count = sum(
        row.get("migration_relevance") == "live-declaration-use"
        for row in candidates.get("rows", [])
    )
    known_metadata_count = max(0, known_live_candidate_count - known_bundle_count)
    shared_bundle_count = sum(
        item["class"] == "shared-structural-bundle"
        for row in rows
        for item in row["declaration_actions"]
    )
    known_action_counts = Counter(action_counts)
    if known_bundle_count:
        known_action_counts["confirmed-bundle-migration"] = known_bundle_count
    if known_metadata_count:
        known_action_counts["metadata-status-use"] = known_metadata_count
    return {
        "schema_version": 1,
        "purpose": "reconciled YM historical Round repair actions",
        "sources": {
            "ledger": ".dashi/round-stranded/ym-consolidation-ledger.json",
            "migration_plan": ".dashi/round-stranded/ym-migration-plan.json",
            "candidates": ".dashi/round-stranded/ym-migration-candidates.json",
            "bundles": ".dashi/round-stranded/ym-live-bundle-plan.json",
            "context_audit": ".dashi/round-stranded/ym-context-audit.json",
            "probe": ".dashi/round-stranded/ym-context-probe.json" if probe else None,
        },
        "edge_counts": {
            "migration_plan_rows": len(plan.get("rows", [])),
            "mapping_incomplete_import_edges": plan.get("status_counts", {}).get("mapping-incomplete", 0),
            "context_repair_import_edges": plan.get("status_counts", {}).get("unused-import-remove-or-recheck", 0),
            "context_audit_rows": len(audit.get("rows", [])),
        },
        "declaration_action_counts": dict(sorted(declaration_counts.items())),
        "unique_declaration_action_counts": dict(sorted(unique_declaration_counts.items())),
        "known_semantic_action_counts": {
            "confirmed-bundle-migration": known_bundle_count,
            "metadata-status-use": known_metadata_count,
            "shared-bundle-migration": shared_bundle_count,
        },
        "action_counts": dict(sorted(known_action_counts.items())),
        "queue_counts": dict(sorted(queue_counts.items())),
        "rows": rows,
        "proof_cone_external": [],
        "policy": {
            "bundle_recipients_are_explicit": True,
            "generic_signature_matches_are_not_mappings": True,
            "probe_passes_are_batch_evidence": True,
            "source_hash_required_for_apply": True,
            "deletion_authorized": False,
            "proof_cone_work_is_separate": True,
            "historical_round_rows_are_migration_scope": True,
        },
        "deletion_authorized": False,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path("."))
    parser.add_argument("--ledger", type=Path, default=Path(".dashi/round-stranded/ym-consolidation-ledger.json"))
    parser.add_argument("--plan", type=Path, default=Path(".dashi/round-stranded/ym-migration-plan.json"))
    parser.add_argument("--candidates", type=Path, default=Path(".dashi/round-stranded/ym-migration-candidates.json"))
    parser.add_argument("--bundles", type=Path, default=Path(".dashi/round-stranded/ym-live-bundle-plan.json"))
    parser.add_argument("--audit", type=Path, default=Path(".dashi/round-stranded/ym-context-audit.json"))
    parser.add_argument("--probe", type=Path, default=Path(".dashi/round-stranded/ym-context-probe.json"))
    parser.add_argument("--output", type=Path, default=Path(".dashi/round-stranded/ym-migration-reconciliation.json"))
    args = parser.parse_args()
    root = args.repo_root.resolve()
    report = build_reconciliation(
        root,
        _read(root / args.ledger),
        _read(root / args.plan),
        _read(root / args.candidates),
        _read(root / args.bundles),
        _read(root / args.audit),
        _read(root / args.probe) if (root / args.probe).is_file() else None,
    )
    output = root / args.output
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({
        "action_counts": report["action_counts"],
        "declaration_action_counts": report["declaration_action_counts"],
        "unique_declaration_action_counts": report["unique_declaration_action_counts"],
        "output": str(output),
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
