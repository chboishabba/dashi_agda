#!/usr/bin/env python3
"""Read-only reusable GenBank -> typed metadata/feature report and candidate graph.

Source attribution stays with each original GenBank author. This is a parser
and ontology review adapter, not a sequence designer, genetic intervention,
or a validated molecular-function model.

Biopython SeqIO (Cock et al., Bioinformatics 2009, DOI 10.1093/bioinformatics/btp163)
provides the source GenBank parser. Original file bytes are never rewritten.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import warnings
from collections import Counter
from io import StringIO
from pathlib import Path
from typing import Any

from Bio import BiopythonParserWarning, SeqIO
from Bio.SeqFeature import CompoundLocation, ExactPosition, SimpleLocation

SCHEMA = "dashi.genbank.readonly.v1"
GRAPH_SCHEMA = "dashi.genbank.candidate-graph.v1"
AUTHORITY = {
    "read_only": True,
    "non_authoritative": True,
    "canonical_truth_mutated": False,
    "candidate_only": True,
    "promotion_authority": False,
}


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def location_tree(location: Any, sequence_length: int) -> dict:
    """Preserve part order, strand and exact 0-based half-open spans."""
    if isinstance(location, CompoundLocation):
        _require(location.operator in {"join", "order"}, "unsupported compound operator")
        _require(len(location.parts) >= 2, "compound needs two or more parts")
        return {
            "kind": "compound",
            "operator": location.operator,
            "strand": location.strand,
            "parts": [location_tree(p, sequence_length) for p in location.parts],
        }
    _require(isinstance(location, SimpleLocation), "unsupported location")
    _require(isinstance(location.start, ExactPosition)
             and isinstance(location.end, ExactPosition),
             "fuzzy or unknown location held for review")
    start, end = int(location.start), int(location.end)
    _require(0 <= start < end <= sequence_length,
             "zero-length/out-of-bounds feature location")
    _require(location.strand in (-1, 0, 1, None), "unsupported strand")
    return {
        "kind": "span", "start0": start, "end0": end,
        "start1": start + 1, "end1": end, "strand": location.strand,
    }


def location_normalize(ast: dict) -> dict:
    """Independent JSON AST validation; no hidden sequence content."""
    _require(isinstance(ast, dict), "invalid location AST")
    if ast.get("kind") == "span":
        start, end = ast.get("start0"), ast.get("end0")
        _require(type(start) is int and type(end) is int and 0 <= start < end,
                 "invalid half-open interval")
        _require(ast.get("start1") == start + 1 and ast.get("end1") == end,
                 "one-based/zero-based coordinate mismatch")
        _require(ast.get("strand") in (-1, 0, 1, None), "invalid strand")
        return {
            "kind": "span", "start0": start, "end0": end,
            "start1": start + 1, "end1": end, "strand": ast["strand"],
        }
    if ast.get("kind") == "compound":
        _require(ast.get("operator") in ("join", "order"),
                 "bad location operator")
        parts = ast.get("parts")
        _require(isinstance(parts, list) and len(parts) >= 2,
                 "compound location needs at least two parts")
        children = [location_normalize(p) for p in parts]
        _require(ast.get("strand") in (-1, 0, 1, None),
                 "bad compound strand")
        return {
            "kind": "compound", "operator": ast["operator"],
            "strand": ast["strand"], "parts": children,
        }
    raise ValueError("unknown location kind")


def _spans(location: dict):
    if location["kind"] == "span":
        yield location
    else:
        for child in location["parts"]:
            yield from _spans(child)


def _sha_object(value: Any) -> str:
    raw = json.dumps(value, ensure_ascii=False, sort_keys=True,
                     separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()


def parse_genbank_bytes(
    raw: bytes, *, source_ref: str,
    creator: str = "source author not yet verified",
    source_revision: str = "unresolved",
) -> dict:
    """Read exactly one GenBank DNA record; emit NO bases or DNA design."""
    _require(bool(raw) and len(raw) <= 100_000_000, "empty/oversize GenBank")
    try:
        source_text = raw.decode("utf-8")
    except UnicodeError as exc:
        raise ValueError("source is not UTF-8 GenBank") from exc

    with warnings.catch_warnings(record=True) as caught:
        warnings.simplefilter("always", BiopythonParserWarning)
        try:
            records = list(SeqIO.parse(StringIO(source_text), "genbank"))
        except Exception as exc:
            raise ValueError("malformed GenBank text") from exc
    parser_warnings = [str(w.message) for w in caught
                       if issubclass(w.category, BiopythonParserWarning)]
    _require(not parser_warnings,
             "GenBank parser warnings: " + "; ".join(parser_warnings))
    _require(len(records) == 1, "expected exactly one GenBank record")
    record = records[0]
    bases = str(record.seq).upper()
    _require(bool(bases) and set(bases) <= set("ACGT"),
             "only concrete A/C/G/T DNA is supported")
    molecule_type = record.annotations.get("molecule_type", "")
    _require(molecule_type in ("DNA", "ds-DNA", "ss-DNA"),
             "missing or unsupported DNA molecule type")
    topology = record.annotations.get("topology")
    _require(topology in ("linear", "circular"),
             "missing/unsupported DNA topology")

    features = []
    for index, feature in enumerate(record.features):
        _require(feature.location is not None,
                 "feature has no location")
        location = location_tree(feature.location, len(bases))
        _require(location_normalize(location) == location,
                 "feature location normalization differs")
        _require(all(0 <= span["start0"] < span["end0"] <= len(bases)
                     for span in _spans(location)),
                 "compound location out of bounds")
        qualifiers = [{"key": key, "values": list(values)}
                      for key, values in feature.qualifiers.items()]
        _require(all(isinstance(q["key"], str)
                     and all(isinstance(v, str) for v in q["values"])
                     for q in qualifiers),
                 "qualifier is not source text")
        features.append({
            "index": index, "type": str(feature.type),
            "location": location,
            "location_as_parsed": str(feature.location),
            "qualifiers": qualifiers,
            "evidence_tier": "source-annotation-only",
        })

    report = {
        "schema": SCHEMA,
        "source": {
            "source_ref": source_ref,
            "creator": creator,
            "source_revision": source_revision,
            "raw_sha256": hashlib.sha256(raw).hexdigest(),
            "raw_byte_count": len(raw),
            "record_id": str(record.id),
            "record_name": str(record.name),
            "internal_date": record.annotations.get("date"),
            "raw_source_retained_externally": True,
        },
        "molecule": {
            "sequence_length": len(bases),
            "alphabet": "ACGT",
            "molecule_type": molecule_type,
            "topology": topology,
            "sequence_sha256": hashlib.sha256(
                bases.encode("ascii")).hexdigest(),
        },
        "feature_count": len(features),
        "feature_types": dict(sorted(
            Counter(item["type"] for item in features).items())),
        "features": features,
    }
    report["semantic_sha256"] = _sha_object(report)
    report["authority_boundary"] = dict(AUTHORITY)
    report["biological_function_verified"] = False
    report["protein_identity_verified"] = False
    return report


def candidate_review_graph(report: dict) -> dict:
    """A candidate-only interoperable *projection*, not an ITIR MCP API."""
    _require(report.get("schema") == SCHEMA,
             "unexpected GenBank report schema")
    _require(report.get("authority_boundary") == AUTHORITY,
             "promoted source report rejected")
    source = report["source"]
    source_id = "genbank-source:" + source["raw_sha256"]
    statements = []
    for feature in report["features"]:
        feature_id = (f"genbank-feature:{source['raw_sha256']}:"
                      f"{feature['index']}")
        statements.append({
            "statement_id": feature_id,
            "subject": source_id,
            "predicate": "artifactHasAnnotatedFeature",
            "object": feature_id,
            "feature_type": feature["type"],
            "location": feature["location"],
            "qualifiers": feature["qualifiers"],
            "status": "candidate",
            "claim_tier": "source-annotation-only",
            "provenance_refs": [
                source["source_ref"],
                source["raw_sha256"], feature_id,
            ],
            "independent_external_ontology_identity_verified": False,
            "repair_disposition": "hold-for-review",
        })
    return {
        "schema": GRAPH_SCHEMA,
        "source_schema": SCHEMA,
        "source_id": source_id,
        "candidate_statements": statements,
        "authority_boundary": dict(AUTHORITY),
        "native_ITIR_or_SLR_API_conformance_claim": False,
        "automatic_wikidata_repair": False,
        "biological_same_object_claim": False,
        "independent_sequence_to_phenotype_proof": False,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("--creator", default="source author not yet verified")
    parser.add_argument("--revision", default="unresolved")
    parser.add_argument("--source-ref")
    parser.add_argument("--graph", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    report = parse_genbank_bytes(
        args.input.read_bytes(),
        source_ref=args.source_ref or args.input.resolve().as_uri(),
        creator=args.creator,
        source_revision=args.revision,
    )
    if args.graph:
        report = candidate_review_graph(report)
    result = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(result, encoding="utf-8")
    else:
        print(result, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
