#!/usr/bin/env python3
"""Read-only GenBank component/replicon ontology projection.

This is a generic annotation interpreter, NOT a genetic design/assembly or
mobile-element selection tool. It consumes the existing DASHI GenBank parser's
sequence-free report. Keys are derived from the INSDC feature table definition,
version 11.4 (2026-04); new/unknown keys remain source-bound, unclassified.

References: INSDC DDBJ/ENA/GenBank Feature Table Definition v11.4;
Cock et al., Biopython, Bioinformatics 2009, DOI 10.1093/bioinformatics/btp163;
DASHI DNAFirstFormalism / GenBankLocationFiniteCore, BH4 ontology and ITIR
candidate-only repair conventions. No implied external ontology equivalence.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from collections import Counter
from pathlib import Path
from typing import Any

SCHEMA_IN = "dashi.genbank.readonly.v1"
SCHEMA_OUT = "dashi.genbank.component-registry.v1"
REVIEW_SCHEMA = "dashi.genbank.component-review.v1"
AUTHORITY = {
    "read_only": True,
    "non_authoritative": True,
    "canonical_truth_mutated": False,
    "candidate_only": True,
    "promotion_authority": False,
}

# These are category aliases for recorded feature keys; they are not claims
# that the author correctly identified the biological function.
KEY_CLASS = {
    "source": "source_metadata",
    "gene": "gene_annotation",
    "CDS": "coding_sequence_annotation",
    "mRNA": "transcript_annotation",
    "tRNA": "transcript_annotation",
    "rRNA": "transcript_annotation",
    "ncRNA": "transcript_annotation",
    "misc_RNA": "transcript_annotation",
    "exon": "transcript_structure",
    "intron": "transcript_structure",
    "promoter": "regulatory_annotation",
    "terminator": "regulatory_annotation",
    "regulatory": "regulatory_annotation",
    "enhancer": "regulatory_annotation",
    "polyA_signal": "regulatory_annotation",
    "polyA_site": "regulatory_annotation",
    "attenuator": "regulatory_annotation",
    "CAAT_signal": "regulatory_annotation",
    "TATA_signal": "regulatory_annotation",
    "rep_origin": "replication_annotation",
    "oriT": "transfer_origin_annotation",
    "mobile_element": "mobile_element_annotation",
    "repeat_region": "repeat_annotation",
    "misc_recomb": "recombination_annotation",
    "protein_bind": "binding_annotation",
    "primer_bind": "binding_annotation",
    "misc_binding": "binding_annotation",
    "stem_loop": "structural_annotation",
    "misc_structure": "structural_annotation",
    "misc_feature": "unclassified_annotation",
}

# INSDC /mobile_element_type controlled vocabulary. The prefix identifies
# the author's annotation, not demonstrated movement in a host.
MOBILE_TYPES = {
    "transposon", "retrotransposon", "integron", "insertion sequence",
    "non-LTR retrotransposon", "SINE", "MITE", "LINE", "other",
}
SOURCE_CONTEXT_KEYS = ("plasmid", "chromosome")
HEX_SHA = re.compile(r"[a-f0-9]{64}\Z")


def _fail(ok: bool, reason: str) -> None:
    if not ok:
        raise ValueError(reason)


def _qualifiers(feature: dict) -> dict[str, list[str]]:
    rows = feature.get("qualifiers")
    _fail(isinstance(rows, list), "missing feature qualifier array")
    out: dict[str, list[str]] = {}
    for row in rows:
        _fail(isinstance(row, dict), "invalid qualifier row")
        key, values = row.get("key"), row.get("values")
        _fail(isinstance(key, str) and bool(key), "invalid qualifier key")
        _fail(isinstance(values, list) and all(isinstance(v, str) for v in values),
              "invalid qualifier values")
        out.setdefault(key, []).extend(values)
    return out


def _location_check(location: dict, n: int) -> dict:
    """Defence in depth on exported typed coordinate AST, never DNA alignment."""
    _fail(isinstance(location, dict), "invalid location AST")
    kind = location.get("kind")
    if kind == "span":
        a, b = location.get("start0"), location.get("end0")
        _fail(type(a) is int and type(b) is int and 0 <= a < b <= n,
              "invalid/out-of-bounds interval")
        _fail(location.get("start1") == a + 1 and location.get("end1") == b,
              "source-internal coordinate mismatch")
        _fail(location.get("strand") in (-1, 0, 1, None), "invalid strand")
        return {"kind": "span", "start0": a, "end0": b,
                "start1": a + 1, "end1": b, "strand": location["strand"]}
    _fail(kind == "compound", "unsupported location AST kind")
    op, parts = location.get("operator"), location.get("parts")
    _fail(op in ("join", "order"), "invalid compound operator")
    _fail(isinstance(parts, list) and len(parts) >= 2, "invalid compound parts")
    _fail(location.get("strand") in (-1, 0, 1, None), "invalid compound strand")
    nodes = [_location_check(p, n) for p in parts]
    # Deliberately preserve ordered children; flattening crosses wrong
    # coordinate/strand boundaries and loses circular origin crossing.
    return {"kind": "compound", "operator": op,
            "strand": location["strand"], "parts": nodes}


def _safe_claim(values: list[str]) -> list[str]:
    """Short identity hints only; preserve exact wording in the original source.

    Do not re-emit base strings, site-change descriptions, or edit/codon notes.
    Users can reopen the exact attributed source, not reconstruct editing plans
    from the candidate graph.
    """
    returned = []
    for v in values:
        if not (1 <= len(v) <= 128) or "\n" in v:
            continue
        if re.fullmatch(r"[ACGTUNacgtun]{8,}", v):
            continue
        if re.search(r"(?i)\b(codon|mutation|sequence change|changed from)\b|->|→", v):
            continue
        returned.append(v)
    return returned


def _hold(owner: str, kind: str, detail: str, refs: list[str]) -> dict:
    identity = hashlib.sha256(json.dumps(
        [owner, kind, detail], separators=(",", ":")
    ).encode("utf-8")).hexdigest()[:24]
    return {
        "id": "genbank-component-hold:" + identity,
        "subject": owner, "diagnostic_origin": kind,
        "reason": detail,
        "source_reopen_refs": refs,
        "repair_disposition": "hold-for-review",
        "review_authority": "candidate-only",
        "external_ontology_mutated": False,
        "biological_identity_or_function_proved": False,
    }


def project_component_registry(report: dict) -> dict:
    _fail(isinstance(report, dict) and report.get("schema") == SCHEMA_IN,
          "unexpected source parser schema")
    _fail(report.get("authority_boundary") == AUTHORITY and
          report.get("biological_function_verified") is False and
          report.get("protein_identity_verified") is False,
          "source parser authority boundary absent or promoted")
    source, molecule, features = report.get("source"), report.get("molecule"), report.get("features")
    _fail(isinstance(source, dict) and isinstance(molecule, dict) and
          isinstance(features, list), "incomplete parser report")
    digest, source_ref = source.get("raw_sha256"), source.get("source_ref")
    _fail(isinstance(digest, str) and bool(HEX_SHA.fullmatch(digest)) and
          isinstance(source_ref, str) and bool(source_ref), "source identity missing")
    _fail(molecule.get("topology") in {"linear", "circular"},
          "unrecognized source topology")
    n = molecule.get("sequence_length")
    _fail(type(n) is int and n > 0 and report.get("feature_count") == len(features),
          "source feature count or sequence length inconsistent")

    source_id = "genbank-source:" + digest
    components: list[dict] = []
    review_holds: list[dict] = []
    replicon_claims: list[dict] = []
    for i, f in enumerate(features):
        _fail(isinstance(f, dict) and f.get("index") == i,
              "source feature order/index mismatch")
        key = f.get("type")
        _fail(isinstance(key, str) and bool(key), "missing source feature key")
        loc = _location_check(f.get("location"), n)
        q = _qualifiers(f)
        component_id = f"genbank-component:{digest}:{i}"
        refs = [source_ref, digest, component_id]
        feature_class = KEY_CLASS.get(key, "unclassified_annotation")
        mobile_type = None
        if key == "mobile_element":
            vals = q.get("mobile_element_type", [])
            if len(vals) != 1:
                review_holds.append(_hold(component_id, "missing_or_ambiguous_mobile_element_type",
                                          "INSDC mobile_element requires one /mobile_element_type", refs))
            else:
                head, sep, tail = vals[0].partition(":")
                if head in MOBILE_TYPES and (head != "other" or (sep and tail)):
                    mobile_type = {"source_type": head,
                                   "source_name": tail if sep else None,
                                   "tier": "source-qualifier-only",
                                   "mobility_experiment_verified": False}
                else:
                    review_holds.append(_hold(component_id, "unrecognized_mobile_element_type",
                                              "not a supported INSDC /mobile_element_type source value", refs))
        elif "mobile_element_type" in q:
            review_holds.append(_hold(component_id, "mobile_type_on_non_mobile_feature",
                                      "qualifier cannot promote another feature key into mobile_element", refs))

        if key == "regulatory" and len(q.get("regulatory_class", [])) != 1:
            review_holds.append(_hold(component_id, "missing_or_ambiguous_regulatory_class",
                                      "INSDC regulatory feature requires a regulatory_class", refs))
        if key == "CDS" and not q.get("product") and not q.get("protein_id"):
            review_holds.append(_hold(component_id, "cds_protein_identity_unresolved",
                                      "CDS annotation is not a verified protein identity", refs))
        if feature_class == "unclassified_annotation" and key not in ("misc_feature",):
            review_holds.append(_hold(component_id, "unrecognized_feature_key",
                                      "retain source key; ontology class unclassified", refs))

        if key == "source":
            for field in SOURCE_CONTEXT_KEYS:
                for value in q.get(field, []):
                    replicon_claims.append({
                        "kind": field, "source_value": value[:128],
                        "source_feature_index": i,
                        "evidence_tier": "source-qualifier-only",
                        "source_reopen_refs": refs,
                    })
        all_source_labels = q.get("label", []) + q.get("gene", [])
        source_labels = _safe_claim(all_source_labels)
        external_refs = _safe_claim(q.get("db_xref", []))
        if source_labels or external_refs:
            review_holds.append(_hold(component_id, "source_label_or_crossref_identity_unverified",
                                      "source claim does not establish external same-object identity", refs))
        components.append({
            "id": component_id, "index": i, "source_feature_key": key,
            "source_feature_class": feature_class,
            "source_location": loc,
            "parser_location_rendering": f.get("location_as_parsed"),
            "original_qualifier_names": [row["key"] for row in f["qualifiers"]],
            "source_short_labels": source_labels,
            "source_labels_withheld_count": len(all_source_labels) - len(source_labels),
            "source_db_xref_candidates": external_refs,
            "mobile_element_type_as_annotated": mobile_type,
            "evidence_tier": "source-feature-annotation-only",
            "source_reopen_refs": refs,
            "externally_curated_identity_verified": False,
            "functional_activity_verified": False,
            "physical_insert_or_mobility_verified": False,
        })
    kinds = {r["kind"] for r in replicon_claims}
    context = (
        "source-annotated-plasmid" if kinds == {"plasmid"} else
        "source-annotated-chromosome" if kinds == {"chromosome"} else
        "source-qualifier-conflict" if len(kinds) > 1 else
        "unresolved"
    )
    if context == "unresolved":
        review_holds.append(_hold(source_id, "record_replicon_context_unresolved",
                                  "topology does not identify plasmid versus chromosome",
                                  [source_ref, digest]))
    elif context == "source-qualifier-conflict":
        review_holds.append(_hold(source_id, "source_replicon_context_conflict",
                                  "conflicting /plasmid and /chromosome source qualifiers",
                                  [source_ref, digest]))
    return {
        "schema": SCHEMA_OUT,
        "source_report_schema": SCHEMA_IN,
        "source": {"id": source_id, "source_ref": source_ref,
                   "creator": source.get("creator"),
                   "source_revision": source.get("source_revision"),
                   "raw_sha256": digest, "raw_byte_count": source.get("raw_byte_count")},
        "record": {
            "sequence_length": n,
            "molecule_type": molecule.get("molecule_type"),
            "topology": molecule["topology"],
            "replicon_context": context,
            "explicit_source_replicon_claims": replicon_claims,
            "circular_implies_plasmid": False,
            "chromosomal_integration_inferred": False,
        },
        "feature_count": len(components),
        "component_classes": dict(sorted(Counter(c["source_feature_class"] for c in components).items())),
        "components": components,
        "review_holds": review_holds,
        "review_hold_count": len(review_holds),
        "source_key_standard": "INSDC feature table v11.4, April 2026",
        "source_key_standard_url": "https://www.insdc.org/submitting-standards/feature-table/",
        "authority_boundary": dict(AUTHORITY),
        "native_ITIR_or_SLR_API_conformance": False,
        "external_Wikidata_edits": False,
        "gene_or_protein_function_verified": False,
        "mobile_element_selection_or_construct_design": False,
        "original_DNA_bases_redistributed": False,
    }


def candidate_review_graph(registry: dict) -> dict:
    _fail(registry.get("schema") == SCHEMA_OUT and
          registry.get("authority_boundary") == AUTHORITY,
          "unexpected/promoted component registry")
    statements = [{
        "statement_id": c["id"],
        "subject": registry["source"]["id"],
        "predicate": "artifactHasSourceAnnotatedComponent",
        "object": c["id"],
        "source_feature_class": c["source_feature_class"],
        "source_feature_key": c["source_feature_key"],
        "source_location": c["source_location"],
        "provenance_refs": c["source_reopen_refs"],
        "status": "candidate", "claim_tier": "source-annotation-only",
        "ontology_equivalence_verified": False,
        "biological_function_verified": False,
    } for c in registry["components"]]
    return {
        "schema": REVIEW_SCHEMA,
        "source_id": registry["source"]["id"],
        "candidate_statements": statements,
        "review_holds": registry["review_holds"],
        "replicon_context": registry["record"]["replicon_context"],
        "authority_boundary": dict(AUTHORITY),
        "native_ITIR_or_SLR_API_conformance": False,
        "external_Wikidata_edits": False,
        "biological_function_verified": False,
    }


def main() -> int:
    cli = argparse.ArgumentParser(description=__doc__)
    inputs = cli.add_mutually_exclusive_group(required=True)
    inputs.add_argument("--report", type=Path, help="Existing DASHI GenBank read-only report JSON")
    inputs.add_argument("--genbank", type=Path, help="Original GenBank file; parsed read-only")
    cli.add_argument("--source-ref", help="Original source or public source URL")
    cli.add_argument("--creator", default="source author not independently verified")
    cli.add_argument("--revision", default="unresolved")
    cli.add_argument("--graph", action="store_true", help="Emit candidate-only ontology graph")
    cli.add_argument("--output", type=Path)
    args = cli.parse_args()
    if args.report:
        report = json.loads(args.report.read_text(encoding="utf-8"))
    else:
        from scripts.genbank_readonly_ingest import parse_genbank_bytes
        report = parse_genbank_bytes(
            args.genbank.read_bytes(),
            source_ref=args.source_ref or args.genbank.resolve().as_uri(),
            creator=args.creator, source_revision=args.revision,
        )
    result = project_component_registry(report)
    if args.graph:
        result = candidate_review_graph(result)
    encoded = json.dumps(result, sort_keys=True, indent=2) + "\n"
    if args.output:
        args.output.write_text(encoded, encoding="utf-8")
    else:
        print(encoded, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
