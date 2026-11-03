#!/usr/bin/env python3
"""Source-reopenable GenBank -> bounded, candidate-only ontology review holds.

DASHI projection based on the BH4/Kitzerow review pattern and the ITIR-suite
Wikidata object-review authority boundary. This is NOT an ITIR MCP/SLR S29
native receipt, public ontology repair or external identity resolution.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from scripts.genbank_readonly_ingest import AUTHORITY, SCHEMA

OUTPUT_SCHEMA = "dashi.genbank.ontology-review-worklist.v1"
USER_STORIES = [
    "ITIR-US-01", "ITIR-US-02", "ITIR-US-17",
    "WIKI-US-01", "WIKI-US-02", "WIKI-US-03", "WIKI-US-04",
]


def stable_id(kind: str, key: str) -> str:
    encoded = json.dumps(
        [kind, key], separators=(",", ":"),
    ).encode("utf-8")
    return "genbank-review:" + hashlib.sha256(encoded).hexdigest()[:24]


def project_review_worklist(report: dict) -> dict:
    if report.get("schema") != SCHEMA or report.get("authority_boundary") != AUTHORITY:
        raise ValueError("source parse absent or authority promoted")
    source = report["source"]
    digest = source["raw_sha256"]
    holds = []

    def add_hold(index: int, kind: str, reason: str, required: str) -> None:
        subject = f"genbank-feature:{digest}:{index}"
        holds.append({
            "id": stable_id(kind, subject),
            "kind": kind,
            "subject": subject,
            "diagnostic_origin": reason,
            "source_role": "source-annotation-only",
            "source_reopen_refs": [
                source["source_ref"], digest, subject,
            ],
            "exact_witness_required": required,
            "proposed_action": "hold-for-review",
            "review_authority": "candidate-only",
            "consumer_adequate": False,
            "edited_external_ontology": False,
            "establishes_claim_truth": False,
            "establishes_protein_function": False,
        })

    for feature in report["features"]:
        qualifiers = {q["key"]: q["values"] for q in feature["qualifiers"]}
        index = feature["index"]
        if "label" in qualifiers:
            add_hold(
                index, "external_identity_review",
                "source_label_not_external_identifier",
                "Source-backed exact protein/gene/Sequence Ontology identity "
                "with revision and feature-coordinate agreement",
            )
        if feature["type"] == "CDS":
            for key in ("gene", "product", "translation", "codon_start"):
                if key not in qualifiers:
                    add_hold(
                        index, "cds_" + key + "_unresolved",
                        "missing_explicit_CDS_qualifier",
                        "Source-authenticated transcript, reading frame, "
                        "isoform and genetic-code context if available",
                    )

    return {
        "schema": OUTPUT_SCHEMA,
        "source_schema": SCHEMA,
        "source_ref": source["source_ref"],
        "source_revision": source["source_revision"],
        "source_digest": digest,
        "review_holds": holds,
        "hold_count": len(holds),
        "user_story_contract_refs": USER_STORIES,
        "authority_boundary": dict(AUTHORITY),
        "native_ITIR_MCP_or_SLR_S29_conformance_claim": False,
        "wikidata_public_edit_permission": False,
        "external_identity_auto_weld": False,
        "biological_phenotype_proven": False,
    }


def main() -> int:
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("report", type=Path)
    cli.add_argument("--output", type=Path)
    args = cli.parse_args()
    report = json.loads(args.report.read_text(encoding="utf-8"))
    work = json.dumps(
        project_review_worklist(report), indent=2, sort_keys=True,
    ) + "\n"
    if args.output:
        args.output.write_text(work, encoding="utf-8")
    else:
        print(work, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
