#!/usr/bin/env python3
"""Read-only full-record GenBank semantic parse/serialize/parse verification.

Biopython source: Cock et al., Bioinformatics 2009,
DOI 10.1093/bioinformatics/btp163.
This does not emit DNA bases, re-design a plasmid, or prove function.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from io import StringIO
from pathlib import Path

from Bio import SeqIO

from scripts.genbank_readonly_ingest import parse_genbank_bytes

SCHEMA = "dashi.genbank.semantic-roundtrip-receipt.v1"


def _feature_signature(report: dict) -> list[dict]:
    return [
        {"type": f["type"], "location": f["location"],
         "qualifiers": f["qualifiers"]}
        for f in report["features"]
    ]


def check_semantic_roundtrip(original: bytes, *, source_ref: str) -> dict:
    before = parse_genbank_bytes(original, source_ref=source_ref)
    reader = StringIO(original.decode("utf-8"))
    records = list(SeqIO.parse(reader, "genbank"))
    if len(records) != 1:
        raise ValueError("exactly one GenBank record required")
    stream = StringIO()
    if SeqIO.write(records[0], stream, "genbank") != 1:
        raise ValueError("GenBank writer emitted unexpected record count")
    normalized = stream.getvalue().encode("utf-8")
    after = parse_genbank_bytes(normalized, source_ref=source_ref)

    checks = {
        "dna_sequence_hash_equal": before["molecule"]["sequence_sha256"]
                                   == after["molecule"]["sequence_sha256"],
        "sequence_length_equal": before["molecule"]["sequence_length"]
                                 == after["molecule"]["sequence_length"],
        "molecule_type_equal": before["molecule"]["molecule_type"]
                               == after["molecule"]["molecule_type"],
        "topology_equal": before["molecule"]["topology"]
                          == after["molecule"]["topology"],
        "feature_types_equal": before["feature_types"]
                               == after["feature_types"],
        "every_feature_location_and_qualifier_equal": (
            _feature_signature(before) == _feature_signature(after)
        ),
        "source_record_id_equal": before["source"]["record_id"]
                                  == after["source"]["record_id"],
    }
    return {
        "schema": SCHEMA,
        "source_ref": source_ref,
        "source_raw_sha256": hashlib.sha256(original).hexdigest(),
        "source_byte_count": len(original),
        "serialized_byte_count": len(normalized),
        "serialized_byte_identical": normalized == original,
        "all_semantic_fields_preserved": all(checks.values()),
        "checks": checks,
        "source_bytes_copied_to_receipt": False,
        "biological_function_verified": False,
        "formal_Agda_or_Lean_kernel_certificate": False,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("original_genbank", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    receipt = check_semantic_roundtrip(
        args.original_genbank.read_bytes(),
        source_ref=args.original_genbank.resolve().as_uri(),
    )
    out = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(out, encoding="utf-8")
    else:
        print(out, end="")
    return 0 if receipt["all_semantic_fields_preserved"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
