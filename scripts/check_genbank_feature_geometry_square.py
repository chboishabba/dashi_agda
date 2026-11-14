#!/usr/bin/env python3
"""GenBank exact feature geometry ↔ reverse-complement commuting-square audit.

Read-only. Uses Biopython's SeqRecord.reverse_complement as an independent
geometry reference and the existing DASHI strict parser as the source owner.
No sequence bases, actionable changes or biological function are emitted.

Agda counterpart: DASHI.Codec.GenBankFeatureGeometrySymmetryExact
(exact, bounded, non-fuzzy *semantic* locations; not raw syntax).
"""
from __future__ import annotations

import argparse
import hashlib
import json
from io import StringIO
from pathlib import Path

from Bio import SeqIO

from scripts.genbank_readonly_ingest import (
    AUTHORITY, location_normalize, parse_genbank_bytes,
)

SCHEMA = "dashi.genbank.feature-geometry-rc-square.v1"


def _reverse_strand(strand):
    if strand is None:
        return None
    if strand in (-1, 0, 1):
        return -strand
    raise ValueError("unsupported source strand")


def mirror_geometry(tree: dict, length: int) -> dict:
    """Flip exact 0-based half-open positions; reverse compound part order."""
    if not isinstance(tree, dict) or type(length) is not int or length <= 0:
        raise ValueError("invalid feature geometry or source length")
    tree = location_normalize(tree)
    if tree["kind"] == "span":
        start, end = tree["start0"], tree["end0"]
        if end > length:
            raise ValueError("location exceeds source length")
        return {
            "kind": "span", "start0": length - end,
            "end0": length - start, "start1": length - end + 1,
            "end1": length - start,
            "strand": _reverse_strand(tree["strand"]),
        }
    # Biopython CompoundLocation._flip (1.86) preserves source part order
    # when ANY part has a defined strand. Only when ALL child strands are
    # None does it reverse part order (circular origin representation).
    # Using compound.strand is insufficient: mixed child strands also
    # yield compound.strand=None yet MUST retain part order.
    source_parts = tree["parts"]
    if all(part["strand"] is None for part in source_parts):
        source_parts = list(reversed(source_parts))
    return {
        "kind": "compound", "operator": tree["operator"],
        "strand": _reverse_strand(tree["strand"]),
        "parts": [mirror_geometry(part, length) for part in source_parts],
    }


def verify_feature_square(raw: bytes, source_ref: str) -> dict:
    original = parse_genbank_bytes(raw, source_ref=source_ref)
    if original.get("authority_boundary") != AUTHORITY:
        raise ValueError("original parse authority must be candidate-only")
    source = SeqIO.read(StringIO(raw.decode("utf-8")), "genbank")
    n = len(source.seq)
    transformed = source.reverse_complement(
        id=True, name=True, description=True,
        features=True, annotations=True,
    )
    rendered = StringIO()
    if SeqIO.write(transformed, rendered, "genbank") != 1:
        raise ValueError("unexpected reverse-complement record count")
    mirrored = parse_genbank_bytes(
        rendered.getvalue().encode("utf-8"), source_ref=source_ref
    )
    if len(original["features"]) != len(mirrored["features"]):
        raise ValueError("reverse-complement changed feature count")
    mismatches: list[int] = []
    for i, (before, after) in enumerate(
        zip(original["features"], mirrored["features"])
    ):
        candidate = mirror_geometry(before["location"], n)
        recovered = mirror_geometry(after["location"], n)
        if (candidate != after["location"]
            or recovered != before["location"]
            or before["type"] != after["type"]
            or before["qualifiers"] != after["qualifiers"]):
            mismatches.append(i)

    # Check the nucleotide carrier's involution separately, without
    # serialising bases into the result (or silently equating it to function).
    s = str(source.seq).upper()
    both = transformed.reverse_complement(
        id=True, name=True, description=True,
        features=True, annotations=True,
    )
    sequence_twice = str(both.seq).upper() == s
    location_twice = all(
        mirror_geometry(mirror_geometry(f["location"], n), n)
        == f["location"]
        for f in original["features"]
    )
    topology_preserved = (
        original["molecule"]["topology"]
        == mirrored["molecule"]["topology"]
    )
    passed = (
        not mismatches and sequence_twice and location_twice
        and topology_preserved
    )
    return {
        "schema": SCHEMA, "source_ref": source_ref,
        "original_raw_sha256": hashlib.sha256(raw).hexdigest(),
        "source_sequence_length": n,
        "topology": original["molecule"]["topology"],
        "original_feature_count": len(original["features"]),
        "reverse_complement_feature_count": len(mirrored["features"]),
        "all_source_feature_geometry_commutes": not mismatches,
        "mismatched_source_feature_indices": mismatches,
        "double_reverse_complement_sequence_equal": sequence_twice,
        "double_reverse_complement_geometry_equal": location_twice,
        "topology_preserved": topology_preserved,
        "all_checks_passed": passed,
        "source_bytes_emitted": False,
        "biological_function_proved": False,
        "kernel_accepted_formal_parser_theorem": False,
        "candidate_only": True,
        "authority_boundary": dict(AUTHORITY),
    }


def main() -> int:
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("original_genbank", type=Path)
    cli.add_argument("--source-ref", default="original-read-only-source")
    cli.add_argument("--output", type=Path)
    args = cli.parse_args()
    receipt = verify_feature_square(
        args.original_genbank.read_bytes(),
        source_ref=args.source_ref,
    )
    text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(text, encoding="utf-8")
    else:
        print(text, end="")
    return 0 if receipt["all_checks_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
