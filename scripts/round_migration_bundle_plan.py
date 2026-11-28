#!/usr/bin/env python3
"""Plan extraction of live source-bearing declarations from Round modules.

This is the bridge between discovery and migration.  It selects only
declarations that are both unresolved at package level and textually used by a
live consumer, then reports the source span, consumers, recipient evidence,
and import closure needed to move the declaration.  It never edits Agda.
"""

from __future__ import annotations

import argparse
import json
import re
from collections import defaultdict
from pathlib import Path
from typing import Any


DECL_START = re.compile(r"^[A-Za-z][A-Za-z0-9_']*[ \t]*:")
IMPORT_START = re.compile(r"^(?:open\s+)?import\s+([A-Za-z0-9_.]+)")


# These are semantic migration decisions established by the repository proof
# search.  The package/ledger matcher can find textual and hash evidence, but
# it cannot distinguish a compiler wrapper from a theorem or from an audit
# coordinate.  Keep that judgment explicit and reviewable instead of allowing
# a mechanically suggested terminal recipient to become an authorization.
SEMANTIC_ACTIONS: dict[tuple[str, str], dict[str, str]] = {
    (
        "DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound275Exact",
        "compileCanonicalBPaymentCore",
    ): {
        "proof_search_role": "compiler-consequence",
        "migration_action": "inline-into-canonical-ursell-payment-bridge",
        "semantic_recipient": "DASHI.Physics.YangMills.BalabanClayCanonicalBUrsellDonorBidiExact",
        "new_proof_obligation": "none-new; preserve the PositiveTransferGapCore compiler",
        "recipient_evidence_note": "The declaration packages an existing payment core; it is not a missing B theorem.",
        "implementation_status": "implemented-in-canonical-ursell-donor; verification-blocked-by-pre-existing-unsafe-import",
    },
    (
        "DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound330Exact",
        "toR310RationalUpperOrderClosure",
    ): {
        "proof_search_role": "compatibility-packaging",
        "migration_action": "replace-terminal-use-with-selected-limit-closure; retain-bridge-until-consumers-rewired",
        "semantic_recipient": "DASHI.Physics.YangMills.YMClayRouteSSelectedLimitClosureExact",
        "new_proof_obligation": "none-new; the terminal route already consumes SelectedLimitUpperClosure",
        "recipient_evidence_note": "This is stronger compatibility packaging around the selected-limit terminal route.",
    },
    (
        "DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound330Exact",
        "canonicalRound330Boundary",
    ): {
        "proof_search_role": "audit-coordinate",
        "migration_action": "inline-required-boundary-projections-into-direct-source-frontier",
        "semantic_recipient": "DASHI.Physics.YangMills.YMClayDirectSourceOSMassGapFrontierExact",
        "new_proof_obligation": "none-new; preserve the existing status/audit projections",
        "recipient_evidence_note": "The live use is a boundary/status coordinate, not a theorem identity.",
    },
    (
        "DASHI.Physics.YangMills.BalabanClayHighestAlphaRound77FiveAnalyticCutsetExact",
        "round77InteractingWitnessFromLocalAndGap",
    ): {
        "proof_search_role": "compiler-consequence",
        "migration_action": "inline-into-same-h-interacting-witness-closure",
        "semantic_recipient": "DASHI.Physics.YangMills.YangMillsDirectSourceOSSameSystemH6Exact",
        "new_proof_obligation": "none-new; use the existing same-H gap and OPE/Ward inputs",
        "recipient_evidence_note": "The witness is a standard compiler consequence of already identified physical inputs.",
    },
    (
        "DASHI.Physics.YangMills.BalabanClayHighestAlphaRound78TopDownThreeAnalyticFrontierExact",
        "literalClaySolutionFromTopDownThree",
    ): {
        "proof_search_role": "compiler-consequence",
        "migration_action": "inline-into-route-s-literal-clay-closure",
        "semantic_recipient": "DASHI.Physics.YangMills.YMClayLiteralTopDownRouteSClosureExact",
        "new_proof_obligation": "none-new; compile the existing A/B/C inputs",
        "recipient_evidence_note": "The constructor assembles the official solution record from existing route inputs.",
    },
    (
        "DASHI.Physics.YangMills.BalabanClayHighestAlphaRound78TopDownThreeAnalyticFrontierExact",
        "continuumYM",
    ): {
        "proof_search_role": "canonical-consumer-residual",
        "migration_action": "retain-as-field-on-existing-literal-top-down-construction; do-not-duplicate",
        "semantic_recipient": "DASHI.Physics.YangMills.YMClayLiteralTopDownRouteSClosureExact",
        "new_proof_obligation": "the UV-to-continuum same-family physical input remains conditional",
        "recipient_evidence_note": "This is substantive input data for the existing construction, not a duplicate theorem to rename.",
    },
}


def declaration_lines(path: Path, names: set[str]) -> dict[str, int]:
    result = {}
    for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        match = re.match(r"^[ \t]*([A-Za-z][A-Za-z0-9_']*)[ \t]*:", line)
        if match and match.group(1) in names:
            result[match.group(1)] = number
    return result


def imports(path: Path) -> list[str]:
    result = []
    for line in path.read_text(encoding="utf-8").splitlines():
        match = IMPORT_START.match(line.strip())
        if match:
            result.append(match.group(1))
    return sorted(set(result))


def build_plan(repo_root: Path, candidates: dict[str, Any], ledger: dict[str, Any],
               migration_plan: dict[str, Any]) -> dict[str, Any]:
    ledger_rows = {row["module"]: row for row in ledger.get("modules", [])}
    used_by: dict[str, list[str]] = defaultdict(list)
    for row in migration_plan.get("rows", []):
        if row.get("status") != "mapping-incomplete":
            continue
        for name in row.get("used_names", []):
            used_by[f"{row['historical_module']}::{name}"].append(row["consumer"])

    groups: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in candidates.get("rows", []):
        if row.get("status") != "unresolved":
            continue
        if row.get("migration_relevance") != "live-declaration-use":
            continue
        groups[row["module"]].append(row)

    bundles = []
    for module, rows in sorted(groups.items()):
        ledger_row = ledger_rows.get(module, {})
        source_path = repo_root / Path(*module.split(".")).with_suffix(".agda")
        names = {row["name"] for row in rows}
        recipient_candidates = ledger_row.get("terminal_recipient_candidates", [])
        preferred = ledger_row.get("preferred_canonical_targets", [])
        recipient = recipient_candidates[0] if len(recipient_candidates) == 1 else None
        if recipient:
            recipient_status = "single-terminal-recipient"
        else:
            recipient_status = "recipient-review-required"
        bundles.append({
            "historical_module": module,
            "source_path": str(source_path.relative_to(repo_root)),
            "declarations": [
                {
                    "source": row["source"],
                    "name": row["name"],
                    "source_line": declaration_lines(source_path, names).get(row["name"]),
                    "consumers": sorted(used_by.get(f"{module}::{row['name']}", [])),
                    "body_hash": row.get("body_sha256", ""),
                    "signature_hash": row.get("signature_sha256", ""),
                    **SEMANTIC_ACTIONS.get((module, row["name"]), {}),
                }
                for row in sorted(rows, key=lambda item: item["name"])
            ],
            "live_consumers": sorted({
                consumer for row in rows
                for consumer in used_by.get(f"{module}::{row['name']}", [])
            }),
            "terminal_recipient_candidates": recipient_candidates,
            "preferred_canonical_targets": preferred,
            "proposed_recipient": recipient,
            "recipient_status": recipient_status,
            "source_imports": imports(source_path) if source_path.is_file() else [],
            "historical_imports_to_rewire": [
                imported for imported in imports(source_path)
                if "Round" in imported or re.search(r"R\d+", imported)
            ],
            "migration_action": ledger_row.get("migration_action"),
            "semantic_actions_complete": all(
                (module, row["name"]) in SEMANTIC_ACTIONS for row in rows
            ),
            "semantic_recipient_notes": sorted({
                action["recipient_evidence_note"]
                for row in rows
                for action in [SEMANTIC_ACTIONS.get((module, row["name"]), {})]
                if action.get("recipient_evidence_note")
            }),
            "implementation_statuses": sorted({
                action["implementation_status"]
                for row in rows
                for action in [SEMANTIC_ACTIONS.get((module, row["name"]), {})]
                if action.get("implementation_status")
            }),
            "policy": "plan-only; no declaration move, import rewrite, or deletion authorized",
        })

    return {
        "schema_version": 2,
        "purpose": "source-bearing Round bundle extraction plan",
        "bundle_count": len(bundles),
        "declaration_count": sum(len(bundle["declarations"]) for bundle in bundles),
        "bundles": bundles,
        "deletion_authorized": False,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path("."))
    parser.add_argument("--candidates", type=Path,
                        default=Path(".dashi/round-stranded/ym-migration-candidates.json"))
    parser.add_argument("--ledger", type=Path,
                        default=Path(".dashi/round-stranded/ym-consolidation-ledger.json"))
    parser.add_argument("--migration-plan", type=Path,
                        default=Path(".dashi/round-stranded/ym-migration-plan.json"))
    parser.add_argument("--output", type=Path,
                        default=Path(".dashi/round-stranded/ym-live-bundle-plan.json"))
    args = parser.parse_args()
    root = args.repo_root.resolve()
    report = build_plan(
        root,
        json.loads((root / args.candidates).read_text(encoding="utf-8")),
        json.loads((root / args.ledger).read_text(encoding="utf-8")),
        json.loads((root / args.migration_plan).read_text(encoding="utf-8")),
    )
    output = root / args.output
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({
        "bundle_count": report["bundle_count"],
        "declaration_count": report["declaration_count"],
        "deletion_authorized": report["deletion_authorized"],
        "output": str(output),
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
