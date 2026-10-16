#!/usr/bin/env python3
"""Acquire one UniProtKB JSON record and emit a bounded provenance certificate.

This script deliberately does not promote UniProt annotations to biological truth.
It records the exact response digest, release headers, selected identity/version
fields, and cross-references so Agda owners can consume a small finite receipt.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
import urllib.error
import urllib.request
from datetime import datetime, timezone
from pathlib import Path


def fetch_uniprot(accession: str) -> tuple[bytes, dict[str, str]]:
    url = f"https://rest.uniprot.org/uniprotkb/{accession}?format=json"
    request = urllib.request.Request(
        url,
        headers={
            "Accept": "application/json",
            "User-Agent": "DASHI-external-biology-acquisition/1.0",
        },
    )
    with urllib.request.urlopen(request, timeout=60) as response:
        raw = response.read()
        headers = {key.lower(): value for key, value in response.headers.items()}
    return raw, headers


def select_cross_references(record: dict) -> list[dict[str, object]]:
    keep = {"PDB", "AlphaFoldDB", "InterPro", "GO", "Rhea", "Reactome", "Ensembl", "RefSeq"}
    selected: list[dict[str, object]] = []
    for xref in record.get("uniProtKBCrossReferences", []):
        database = xref.get("database")
        if database in keep:
            selected.append(
                {
                    "database": database,
                    "id": xref.get("id"),
                    "properties": xref.get("properties", []),
                }
            )
    return selected


def build_certificate(accession: str, raw: bytes, headers: dict[str, str]) -> dict:
    record = json.loads(raw)
    sequence = record.get("sequence", {})
    return {
        "certificate_schema": "dashi.external-biology.uniprot.v1",
        "acquired_at_utc": datetime.now(timezone.utc).isoformat(),
        "request": f"https://rest.uniprot.org/uniprotkb/{accession}?format=json",
        "raw_sha256": hashlib.sha256(raw).hexdigest(),
        "http_release": headers.get("x-uniprot-release"),
        "http_release_date": headers.get("x-uniprot-release-date"),
        "primary_accession": record.get("primaryAccession"),
        "entry_name": record.get("uniProtkbId"),
        "entry_type": record.get("entryType"),
        "entry_audit": record.get("entryAudit", {}),
        "organism": record.get("organism", {}),
        "sequence": {
            "length": sequence.get("length"),
            "mol_weight": sequence.get("molWeight"),
            "crc64": sequence.get("crc64"),
            "md5": sequence.get("md5"),
        },
        "cross_references": select_cross_references(record),
        "promotion_boundary": {
            "database_assertion_creates_biological_truth": False,
            "reviewed_status_implies_direct_experimental_proof": False,
            "cross_reference_creates_same_object_identity": False,
            "certificate_creates_downstream_applicability": False,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("accession", help="UniProtKB accession, e.g. P09417")
    parser.add_argument("-o", "--output", type=Path, help="Write certificate JSON here; default stdout")
    args = parser.parse_args()

    accession = args.accession.strip().upper()
    try:
        raw, headers = fetch_uniprot(accession)
        certificate = build_certificate(accession, raw, headers)
    except (urllib.error.URLError, urllib.error.HTTPError, TimeoutError, json.JSONDecodeError) as exc:
        print(f"UniProt acquisition failed for {accession}: {exc}", file=sys.stderr)
        return 2

    rendered = json.dumps(certificate, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding="utf-8")
    else:
        sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
