#!/usr/bin/env python3
"""Source-verified creator GenBank feature -> avian hypothesis crosswalk.

The original 2020 file is a published digital design, NOT an animal/human
phenotype demonstration. The 2019 Nimpf paper owns vestibular hypothesis
science; The Thought Emporium / Justin Atkin owns the livestream and design.
Independent CRY4/hepatic studies remain contextual and not construct parts.

Requires the exact original creator Git blob verified in this process.
No original DNA bases, target design, plasmid editing or protocol emitted.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from scripts.genbank_readonly_ingest import (
    AUTHORITY, candidate_review_graph, parse_genbank_bytes,
)
from scripts.check_genbank_source_inventory import verify_inspected_source

SCHEMA = "dashi.genbank.magnetoreception-evidence-crosswalk.v1"
FILE_SOURCE = (
    "https://github.com/thethoughtemporium/"
    "Whose-gene-is-it-anyway/tree/master/magnetoreception"
)
NIMPF_DOI = "10.1016/j.cub.2019.09.048"
VIDEO_SOURCE = "The Thought Emporium, Whose Gene #11, 2020-06-17"


def build_source_crosswalk(
    report: dict, inventory: dict, source_parity: dict,
) -> dict:
    """Only valid after independently checking the original raw Git blob."""
    if not (
        source_parity.get("original_blob_identity_matches") is True
        and source_parity.get("all_source_features_match") is True
        and not source_parity.get("problems")
        and report.get("authority_boundary") == AUTHORITY
        and inventory.get("authority_boundary") == AUTHORITY
    ):
        raise ValueError("unverified original file, inventory or authority")
    if inventory["source"]["git_blob_sha"] != source_parity["source_blob_sha"]:
        raise ValueError("source mismatch between parity and inventory")
    if report.get("feature_count") != 22 or len(report.get("features", [])) != 22:
        raise ValueError("wrong source feature count")

    gene_label_feature = report["features"][8]
    labels = [
        v for q in gene_label_feature["qualifiers"]
        if q["key"] == "label" for v in q["values"]
    ]
    if not (gene_label_feature["index"] == 8
            and gene_label_feature["type"] == "misc_feature"
            and labels == ["cacna1d human plus pigeon"]):
        raise ValueError("source feature-label/type disagreement")

    graph = candidate_review_graph(report)
    subject = graph["candidate_statements"][8]["object"]
    return {
        "schema": SCHEMA,
        "source_ref": report["source"]["source_ref"],
        "original_git_blob_sha": inventory["source"]["git_blob_sha"],
        "source_commit": inventory["source"]["source_commit"],
        "creator": inventory["source"]["creator"],
        "source_parity": source_parity,
        "annotated_feature_count": report["feature_count"],
        "mechanism_links": [
            {
                "subject": subject,
                "source_feature_index": 8,
                "feature_type_in_original": "misc_feature",
                "source_label": labels[0],
                "predicate": "creatorDesignLabelDiscussedWithCandidateHypothesis",
                "object": "DASHI.Biology.MagnetoreceptionSurface.vestibularCandidateChannel",
                "original_source_references": [VIDEO_SOURCE, NIMPF_DOI],
                "evidence_role": "creator-interpretation-plus-primary-hypothesis",
                "status": "candidate",
                "protein_same_object_verified": False,
                "editing_effectiveness_verified": False,
                "magnetoreception_phenotype_verified": False,
            }
        ],
        "contextual_comparison_only": [
            {
                "mechanism": "retinal-cryptochrome",
                "primary_source": "10.1038/s41586-021-03618-9",
                "encoded_as_feature_in_design_claim": False,
                "not_a_sequence_absence_proof": True,
            },
            {
                "mechanism": "hepatic-macrophages",
                "primary_source": "10.1126/science.ady2486",
                "encoded_as_feature_in_design_claim": False,
                "not_a_sequence_absence_proof": True,
            },
        ],
        "unverified_claims": [
            "CDS frame and same-object protein identity",
            "cross-species splice isoform and expression",
            "magnetic-field-to-neuron quantitative transduction",
            "perceptual or navigation gain of function",
            "intervention safety and human efficacy",
        ],
        "authority_boundary": dict(AUTHORITY),
        "ontology_or_wikidata_truth_promoted": False,
        "native_ITIR_or_SLR_graph_ingested": False,
        "original_sequence_emitted": False,
    }


def main() -> int:
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("original_genbank", type=Path)
    cli.add_argument(
        "--inventory", type=Path,
        default=Path(
            "docs/biology/data/"
            "ThoughtEmporiumMagnetoreceptionGenBankSourceInventory.json"
        ),
    )
    cli.add_argument("--output", type=Path)
    args = cli.parse_args()
    raw = args.original_genbank.read_bytes()
    inventory = json.loads(args.inventory.read_text(encoding="utf-8"))
    report = parse_genbank_bytes(
        raw, source_ref=FILE_SOURCE,
        creator=inventory["source"]["creator"],
        source_revision=inventory["source"]["source_commit"],
    )
    receipt = verify_inspected_source(report, inventory, raw)
    crosswalk = build_source_crosswalk(report, inventory, receipt)
    result = json.dumps(crosswalk, sort_keys=True, indent=2) + "\n"
    if args.output:
        args.output.write_text(result, encoding="utf-8")
    else:
        print(result, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
