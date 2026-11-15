#!/usr/bin/env python3
"""Exact-input adapter for ITIR-suite itir_mcp.domain_tools.wikidata_review_packet.

Uses the native ITIR tool *when installed*. Does not fake its response or
claim recipient conformance based on a similar JSON schema. All statements
are about source-annotated GenBank features, not verified Wikidata claims.
External source labels are not converted to invented QIDs/ontology identity.

Source contracts: ITIR-suite itir-mcp/src/itir_mcp/domain_tools.py
  WIKIDATA_REVIEW_PACKET_VERSION=itir.wikidata.review_packet.v1
  wikidata_review_packet(payload: Mapping[str,Any])
Original work: ITIR/SensibLaw contributors; original GenBank source creators.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from scripts.genbank_component_registry import (
    AUTHORITY, SCHEMA_OUT, candidate_review_graph,
)

SCHEMA = "dashi.genbank.itir-review-input.v1"
NATIVE_VERSION = "itir.wikidata.review_packet.v1"


def build_native_review_input(registry: dict) -> dict:
    if not isinstance(registry, dict) or registry.get("schema") != SCHEMA_OUT:
        raise ValueError("expected verified component registry schema")
    if registry.get("authority_boundary") != AUTHORITY:
        raise ValueError("component registry cannot carry promotion authority")
    if registry.get("gene_or_protein_function_verified") is not False:
        raise ValueError("unexpected source-to-function promotion")
    graph = candidate_review_graph(registry)
    source = registry["source"]
    provenance = [source["source_ref"], source["raw_sha256"]]
    facts = []
    for c in registry["components"]:
        if (c.get("evidence_tier") != "source-feature-annotation-only"
            or c.get("externally_curated_identity_verified") is not False
            or c.get("functional_activity_verified") is not False):
            raise ValueError("source annotations promoted to evidence")
        facts.append({
            "statement_id": c["id"],
            "fact": "GenBank source-annotated feature "
                + str(c["index"]) + ", key " + c["source_feature_key"]
                + ", class " + c["source_feature_class"],
            "status": "candidate",
            "provenance_refs": c["source_reopen_refs"],
        })
    if not facts:
        raise ValueError("ITIR native review requires at least one source feature")
    constraints = [{
        "constraint_id": h["id"],
        "message": "Source annotation review hold: " + h["diagnostic_origin"],
        "status": "diagnostic", "severity": "info",
        "candidate_refs": [h["subject"]],
        "provenance_refs": h["source_reopen_refs"],
    } for h in registry["review_holds"]]
    # The real native ITIR helper rejects an empty constraints array.
    # This is a nonpromotion invariant, not an invented biological defect.
    constraints.append({
        "constraint_id": "genbank:source-only-nonauthority:" + source["raw_sha256"],
        "message": "GenBank source annotations cannot grant external ontology or biological truth",
        "status": "diagnostic", "severity": "info",
        "candidate_refs": [f["statement_id"] for f in facts],
        "provenance_refs": provenance,
    })
    native_input = {
        "statements": facts, "constraints": constraints,
        "provenance_refs": provenance,
        "tooling_profile": {
            "tool_id": "dashi.genbank.readonly-component-interop",
            "kind": "genbank-source-review",
            "max_authority": "candidate-only",
            "validation_mode": "source-annotation-geometry-checked",
            "repair_mode": "hold-for-review",
            "promotion_requires_gate": True,
            "candidate_only": True,
            "non_authoritative": True,
            "read_only": True,
            "authority_boundary": dict(AUTHORITY),
        },
    }
    return {
        "schema": SCHEMA,
        "native_target_tool": "itir_mcp.domain_tools.wikidata_review_packet",
        "expected_native_version": NATIVE_VERSION,
        "input": native_input,
        "source_identity": {
            "source_ref": source["source_ref"],
            "raw_sha256": source["raw_sha256"],
        },
        "candidate_statements": len(facts),
        "review_constraints": len(constraints),
        "no_external_QID_synthesised": True,
        "native_tool_executed": False,
        "source_bases_emitted": False,
        "authority_boundary": dict(AUTHORITY),
    }


def invoke_native_itir(candidate: dict, itir_src: Path | None = None) -> dict:
    """Actually run real ITIR consumer; fail closed when not installed.

    A native result, if produced, is still a *review* packet, not accepted
    external ontology truth or a claim that an ITIR persistent store changed.
    """
    if candidate.get("schema") != SCHEMA or candidate.get("authority_boundary") != AUTHORITY:
        raise ValueError("invalid ITIR input or authority")
    if itir_src is not None:
        src_path = itir_src.resolve()
        if not (src_path / "itir_mcp" / "domain_tools.py").is_file():
            raise ValueError("--itir-src must point to ITIR-suite/itir-mcp/src")
        sys.path.insert(0, str(src_path))
    try:
        from itir_mcp.domain_tools import wikidata_review_packet
    except ImportError as exc:
        raise RuntimeError(
            "ITIR native domain_tools package unavailable; no native "
            "conformance receipt was created"
        ) from exc
    result = wikidata_review_packet(candidate["input"])
    if (
        result.get("version") != NATIVE_VERSION
        or result.get("domain") != "wikidata"
        or result.get("packet_kind") != "candidate_review_packet"
        or result.get("statement_count") != candidate["candidate_statements"]
        or result.get("constraint_count") != candidate["review_constraints"]
        or result.get("candidate_only") is not True
        or result.get("non_authoritative") is not True
        or result.get("promoted_claims") is not False
        or result.get("truth_claims") is not False
        or result.get("authority_boundary", {}).get("promotion_authority") is not False
    ):
        raise ValueError("native ITIR review output contract mismatch")
    return {
        "schema": "dashi.genbank.itir-native-execution-receipt.v1",
        "native_tool_executed": True,
        "native_version": result["version"],
        "statement_count": result["statement_count"],
        "constraint_count": result["constraint_count"],
        "source_sha256": candidate["source_identity"]["raw_sha256"],
        "candidate_only": True,
        "external_wikidata_edited": False,
        "persistent_ITIR_or_SLR_store_changed": False,
        "experimental_biological_function_verified": False,
        "authority_boundary": dict(AUTHORITY),
    }


def main() -> int:
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("registry_json", type=Path)
    cli.add_argument("--itir-src", type=Path, help="Native ITIR-suite/itir-mcp/src")
    cli.add_argument("--execute-native", action="store_true")
    cli.add_argument("--output", type=Path)
    args = cli.parse_args()
    registry = json.loads(args.registry_json.read_text(encoding="utf-8"))
    payload = build_native_review_input(registry)
    if args.execute_native:
        payload = invoke_native_itir(payload, args.itir_src)
    encoded = json.dumps(payload, sort_keys=True, indent=2) + "\n"
    if args.output:
        args.output.write_text(encoded, encoding="utf-8")
    else:
        print(encoded, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
