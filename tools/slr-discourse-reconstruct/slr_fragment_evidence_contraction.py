#!/usr/bin/env python3
from __future__ import annotations

import argparse
import copy
import json
import sys
from pathlib import Path
from typing import Any

SCHEMA = "slr-fragment-evidence-contraction-v2"
TARGET_SCHEMA = "sl.candidate_world_model.v0_1"
RESIDUAL_SCHEMA = "abc730-canonical-claim-residual-map-v1"
PAYMENT_SCHEMA = "abc730-c029-evidence-payment-receipts-v1"


def load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise SystemExit(f"expected JSON object: {path}")
    return value


def stable_source_id(manifest: dict[str, Any]) -> str:
    return str((manifest.get("ibrahim") or {}).get("stable_source_id", ""))


def claim_nodes(model: dict[str, Any]) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    for node in model.get("claims", []):
        if not isinstance(node, dict):
            continue
        ref = str((node.get("metadata") or {}).get("claim_ref", ""))
        if node.get("node_kind") == "canonical_claim_reference" and ref:
            out[ref] = node
    return out


def valid_payment(receipt: dict[str, Any]) -> bool:
    return all(
        [
            bool(receipt.get("target_obligation_weld_paid", False)),
            bool(receipt.get("claim_role_weld_paid", False)),
            bool(receipt.get("evidence_kind_compatible", False)),
            bool(receipt.get("reviewed_for_payment", False)),
            bool(receipt.get("pays_obligation", False)),
        ]
    )


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--world", type=Path, required=True)
    p.add_argument("--evidence-manifest", type=Path, required=True)
    p.add_argument("--residual-map", type=Path)
    p.add_argument("--payments", type=Path)
    p.add_argument("--output-model", type=Path, required=True)
    p.add_argument("--output-sidecar", type=Path, required=True)
    p.add_argument("--output-gates", type=Path)
    p.add_argument("--output-report", type=Path)
    return p.parse_args()


def main() -> int:
    args = parse_args()
    model = load(args.world)
    manifest = load(args.evidence_manifest)
    if model.get("schema_version") != TARGET_SCHEMA:
        raise SystemExit("unexpected CandidateWorldModel schema")
    if bool((model.get("metadata") or {}).get("semantic_promotion", False)):
        raise SystemExit("refusing semantically promoted world model")

    evidence_id = stable_source_id(manifest)
    if not evidence_id:
        raise SystemExit("evidence manifest missing Ibrahim stable_source_id")

    residual_map: dict[str, Any] = {}
    payments: dict[str, Any] = {}
    if args.residual_map:
        residual_map = load(args.residual_map)
        if residual_map.get("schema") != RESIDUAL_SCHEMA:
            raise SystemExit("unexpected residual-map schema")
        if bool(residual_map.get("semantic_promotion", False)):
            raise SystemExit("residual map must not claim semantic promotion")
    if args.payments:
        payments = load(args.payments)
        if payments.get("schema") != PAYMENT_SCHEMA:
            raise SystemExit("unexpected payment-receipt schema")
        if bool(payments.get("semantic_promotion", False)):
            raise SystemExit("payment receipts must not claim semantic promotion")
    if bool(args.residual_map) != bool(args.payments):
        raise SystemExit("consumer obligation contraction requires both --residual-map and --payments")

    canonical = claim_nodes(model)
    out = copy.deepcopy(model)
    contractions: list[dict[str, Any]] = []
    attribution_paid = 0
    attribution_open = 0
    intermediate_count = 0

    for node in out.get("claims", []):
        if not isinstance(node, dict):
            continue
        kind = str(node.get("node_kind", ""))
        if kind not in {"canonical_claim_local_fragment", "intermediate_discourse_fragment"}:
            continue
        md = node.setdefault("metadata", {})
        residual = node.setdefault("residual", {})
        fragment_id = str(node.get("node_id", ""))
        claim_ref = str(md.get("claim_ref", ""))

        if kind == "intermediate_discourse_fragment" or not claim_ref:
            state = "not-applicable-intermediate"
            intermediate_count += 1
            current_source_id = ""
            speaker_status = ""
            paid = False
        else:
            cnode = canonical.get(claim_ref, {})
            cmd = cnode.get("metadata") or {}
            current_source_id = str(cmd.get("current_primary_source_stable_id", ""))
            speaker_status = str(cmd.get("current_primary_status", ""))
            paid = bool(current_source_id and current_source_id == evidence_id and speaker_status == "verified")
            state = "attribution-source-contracted" if paid else "evidence-open"
            attribution_paid += int(paid)
            attribution_open += int(not paid)

        receipt_id = f"fragment-evidence:{fragment_id}"
        md["fragment_evidence_contraction_ref"] = receipt_id
        residual["attribution_source_dimension"] = "paid" if paid else ("not-applicable" if kind == "intermediate_discourse_fragment" else "open")
        residual["whole_claim_extent_paid"] = False
        residual["claim_truth_promoted"] = False

        contractions.append({
            "receipt_id": receipt_id,
            "fragment_id": fragment_id,
            "fragment_kind": kind,
            "claim_ref": claim_ref,
            "contraction_state": state,
            "fragment_provenance_anchor_ids": list(node.get("source_anchor_ids") or []),
            "evidence_source_stable_id": evidence_id,
            "canonical_claim_primary_source_stable_id": current_source_id,
            "canonical_claim_primary_status": speaker_status,
            "attribution_source_paid": paid,
            "whole_claim_extent_paid": False,
            "claim_truth_promoted": False,
            "semantic_promotion": False,
        })

    # Second contraction surface: canonical consumer obligations inherited by
    # claim-local fragments. Historical residual rows are retained unchanged;
    # later payment rows and an active-view report are appended.
    map_claims = (residual_map.get("claims") or {}) if residual_map else {}
    payment_rows = [r for r in (payments.get("receipts") or []) if isinstance(r, dict)] if payments else []
    by_obligation: dict[str, list[dict[str, Any]]] = {}
    for receipt in payment_rows:
        oid = str(receipt.get("obligation_id", ""))
        if oid:
            by_obligation.setdefault(oid, []).append(receipt)

    current_by_claim: dict[str, dict[str, Any]] = {}
    paid_obligation_ids: set[str] = set()
    partial_or_nonpaying = 0
    rejected_invalid_paying = 0
    append_rows: list[dict[str, Any]] = []

    for claim_ref, spec in map_claims.items():
        if not isinstance(spec, dict):
            continue
        states: list[dict[str, Any]] = []
        for obligation in [o for o in (spec.get("obligations") or []) if isinstance(o, dict)]:
            oid = str(obligation.get("obligation_id", ""))
            receipts = by_obligation.get(oid, [])
            paying = [r for r in receipts if valid_payment(r)]
            nonpaying = [r for r in receipts if not valid_payment(r)]
            partial_or_nonpaying += len(nonpaying)
            rejected_invalid_paying += sum(
                1 for r in nonpaying if bool(r.get("pays_obligation", False))
            )
            paid_now = bool(paying)
            if paid_now:
                paid_obligation_ids.add(oid)
            states.append({
                "obligation_id": oid,
                "prior_status": obligation.get("status", "open"),
                "current_status": "paid" if paid_now else obligation.get("status", "open"),
                "active": not paid_now,
                "paying_receipt_ids": [str(r.get("receipt_id", "")) for r in paying],
                "nonpaying_receipt_ids": [str(r.get("receipt_id", "")) for r in nonpaying],
                "owner_reference": obligation.get("owner_reference", ""),
                "evidence_kind_required": obligation.get("evidence_kind_required", ""),
            })
            for receipt in receipts:
                rid = str(receipt.get("receipt_id", ""))
                append_rows.append({
                    "residual_id": f"obligation-payment:{claim_ref}:{oid}:{rid}",
                    "candidate_id": f"canonical-claim:{claim_ref}",
                    "status": "candidate",
                    "residual_kind": "canonical_claim_obligation_payment_receipt",
                    "canonical_claim_ref": claim_ref,
                    "obligation_id": oid,
                    "receipt_id": rid,
                    "payment_disposition": receipt.get("payment_disposition", ""),
                    "payment_valid": valid_payment(receipt),
                    "pays_obligation": bool(receipt.get("pays_obligation", False)),
                    "evidence_reference": receipt.get("evidence_reference", ""),
                    "residual": receipt.get("residual", ""),
                    "historical_obligation_rewritten": False,
                    "claim_truth_promoted": False,
                    "semantic_promotion": False,
                })
        active = [state for state in states if state["active"]]
        current_by_claim[str(claim_ref)] = {
            "claim_ref": claim_ref,
            "consumer_reference": spec.get("consumer_reference", ""),
            "obligations": states,
            "active_obligation_ids": [state["obligation_id"] for state in active],
            "current_first_residual": active[0]["obligation_id"] if active else "none",
            "consumer_adequate": len(active) == 0,
        }

    residuals = list(out.get("residuals") or [])
    existing_residual_ids = {
        str(row.get("residual_id", "")) for row in residuals if isinstance(row, dict)
    }
    appended_payment_rows = 0
    for row in append_rows:
        rid = str(row.get("residual_id", ""))
        if rid and rid not in existing_residual_ids:
            residuals.append(row)
            existing_residual_ids.add(rid)
            appended_payment_rows += 1
    out["residuals"] = residuals

    candidate_adequacy: dict[str, bool] = {}
    if current_by_claim:
        for node in out.get("claims", []):
            if not isinstance(node, dict):
                continue
            node_id = str(node.get("node_id", ""))
            md = node.get("metadata") or {}
            claim_ref = str(md.get("claim_ref", ""))
            if node_id.startswith("canonical-claim:") and not claim_ref:
                claim_ref = node_id.split("canonical-claim:", 1)[1]
            if claim_ref in current_by_claim:
                candidate_adequacy[node_id] = bool(current_by_claim[claim_ref]["consumer_adequate"])

    out.setdefault("projections", []).append({
        "projection_id": SCHEMA,
        "projection_kind": "append_only_fragment_evidence_contraction",
        "status": "candidate",
        "evidence_source_stable_id": evidence_id,
        "sidecar": str(args.output_sidecar),
        "consumer_obligation_payment_view_attached": bool(current_by_claim),
        "semantic_promotion": False,
    })
    out.setdefault("update_rules", []).append({
        "rule_id": "slr-fragment-evidence-append-only-v2",
        "rule_kind": "append_only_evidence_contraction",
        "description": "Evidence may contract attribution or consumer-obligation dimensions through later receipts without rewriting fragment provenance, historical residual rows, whole-claim extent, or claim truth.",
        "semantic_promotion": False,
    })
    meta = out.setdefault("metadata", {})
    meta["fragment_evidence_contraction"] = {
        "schema": SCHEMA,
        "evidence_source_stable_id": evidence_id,
        "fragment_provenance_is_evidence_authority": False,
        "evidence_authority_rewrites_fragment_provenance": False,
        "historical_residuals_rewritten": False,
        "consumer_obligation_payment_view_attached": bool(current_by_claim),
        "paid_obligation_ids": sorted(paid_obligation_ids),
        "whole_claim_extent_paid": False,
        "claim_truth_promoted": False,
        "candidate_only": True,
        "semantic_promotion": False,
    }

    c029 = current_by_claim.get("ABC730-2026-09-09-C029", {})
    c029_adequate = bool(c029.get("consumer_adequate", False))
    c029_first = str(c029.get("current_first_residual", "unsupplied"))

    sidecar = {
        "schema": SCHEMA,
        "target_schema": TARGET_SCHEMA,
        "source_model_id": model.get("model_id", ""),
        "evidence_source_stable_id": evidence_id,
        "contractions": contractions,
        "consumer_obligation_active_view": current_by_claim,
        "summary": {
            "fragments": len(contractions),
            "attribution_source_paid": attribution_paid,
            "evidence_open": attribution_open,
            "intermediate_fragments": intermediate_count,
            "payment_receipt_count": len(payment_rows),
            "appended_payment_receipt_count": appended_payment_rows,
            "paid_obligation_count": len(paid_obligation_ids),
            "partial_or_nonpaying_receipt_count": partial_or_nonpaying,
            "rejected_invalid_paying_receipt_count": rejected_invalid_paying,
            "c029_consumer_adequate": c029_adequate,
            "c029_current_first_residual": c029_first,
        },
        "payment_rules": {
            "requires_target_obligation_weld": True,
            "requires_claim_role_weld": True,
            "requires_evidence_kind_compatibility": True,
            "requires_review": True,
            "requires_explicit_pays_obligation": True,
        },
        "fragment_provenance_is_evidence_authority": False,
        "evidence_authority_rewrites_fragment_provenance": False,
        "historical_residuals_rewritten": False,
        "whole_claim_extent_paid": False,
        "claim_truth_promoted": False,
        "candidate_only": True,
        "semantic_promotion": False,
        "append_only": True,
    }

    gates = None
    if args.output_gates:
        gates = {
            "schema": "c029-consumer-gates-v1",
            "consumer_reference": "ABC730 C029 unintended-consequences comparative/evaluative consumer",
            "consumer_adequate": None,
            "candidate_adequacy": candidate_adequacy,
            "current_residual": c029_first,
            "evaluate_aptness_enabled": c029_adequate,
            "legal_cutset_reference": "DASHI.Policy.ABC730C029LegalMachineryHyperfabricExact.canonicalC029Cutset",
            "world_constraint_reference": "DASHI.Interop.SLRC029WorldConstraintFibreBridgeExact.canonicalC029WorldConstraintState",
            "gate_state_role": "derived-structural-consumer-admission-state-not-empirical-evidence",
            "derived_from_contraction_sidecar": str(args.output_sidecar),
            "candidate_only": True,
            "semantic_promotion": False,
            "truth_promoted": False,
        }

    report = {
        "schema": SCHEMA,
        "target_schema": TARGET_SCHEMA,
        "claims": current_by_claim,
        "summary": sidecar["summary"],
        "rules": sidecar["payment_rules"],
        "historical_residuals_rewritten": False,
        "claim_truth_promoted": False,
        "candidate_only": True,
        "semantic_promotion": False,
    }

    args.output_model.parent.mkdir(parents=True, exist_ok=True)
    args.output_sidecar.parent.mkdir(parents=True, exist_ok=True)
    args.output_model.write_text(json.dumps(out, indent=2, ensure_ascii=False, sort_keys=True) + "\n", encoding="utf-8")
    args.output_sidecar.write_text(json.dumps(sidecar, indent=2, ensure_ascii=False, sort_keys=True) + "\n", encoding="utf-8")
    if args.output_gates and gates is not None:
        args.output_gates.parent.mkdir(parents=True, exist_ok=True)
        args.output_gates.write_text(json.dumps(gates, indent=2, ensure_ascii=False, sort_keys=True) + "\n", encoding="utf-8")
    if args.output_report:
        args.output_report.parent.mkdir(parents=True, exist_ok=True)
        args.output_report.write_text(json.dumps(report, indent=2, ensure_ascii=False, sort_keys=True) + "\n", encoding="utf-8")

    print(
        "SLR_FRAGMENT_EVIDENCE_CONTRACTION_RECEIPT "
        f"schema={SCHEMA} fragments={len(contractions)} attribution_source_paid={attribution_paid} "
        f"evidence_open={attribution_open} intermediate_fragments={intermediate_count} "
        f"payment_receipts={len(payment_rows)} paid_obligations={len(paid_obligation_ids)} "
        f"partial_or_nonpaying={partial_or_nonpaying} rejected_invalid_paying={rejected_invalid_paying} "
        f"c029_adequate={str(c029_adequate).lower()} c029_first_residual={c029_first} "
        "fragment_provenance_is_evidence_authority=false evidence_authority_rewrites_fragment_provenance=false "
        "historical_residuals_rewritten=false whole_claim_extent_paid=false candidate_only=true "
        "semantic_promotion=false claim_truth_promoted=false append_only=true",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
