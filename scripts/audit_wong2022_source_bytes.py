#!/usr/bin/env python3
"""Local source-byte digest receipts for Wong et al. (2022).

No network fetch, workbook chemical analysis, PDF text extraction, procedure
or experimental synthesis. A digest identifies *provided local bytes*; it
does not authenticate that they came from the publisher, belong to a given
figure, support a claim, or constitute independent scientific verification.

Original paper: Wong, Lim, Tan, Go, Bell, Freemont, Yew.
Nature Communications 13:712. DOI 10.1038/s41467-022-28386-6.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import zipfile
from pathlib import Path

DOI = "10.1038/s41467-022-28386-6"
SOURCE_URL = "https://www.nature.com/articles/s41467-022-28386-6"
CHUNK_SIZE = 1024 * 1024


def file_digest_receipt(
    path: Path,
    *,
    kind: str,
    independently_expected_sha256: str | None = None,
) -> dict:
    """Hash provided bytes and validate only a shallow container signature."""
    if kind not in ("source_data_xlsx", "supplementary_pdf"):
        raise ValueError("kind must be source_data_xlsx or supplementary_pdf")
    if not path.is_file():
        raise FileNotFoundError(path)
    if kind == "source_data_xlsx":
        if path.suffix.lower() != ".xlsx" or not zipfile.is_zipfile(path):
            raise ValueError("source_data_xlsx requires an .xlsx ZIP container")
        with zipfile.ZipFile(path) as archive:
            if "xl/workbook.xml" not in archive.namelist():
                raise ValueError("source_data_xlsx has no xl/workbook.xml")
    else:
        if path.suffix.lower() != ".pdf":
            raise ValueError("supplementary_pdf requires a .pdf extension")
        with path.open("rb") as stream:
            if stream.read(5) != b"%PDF-":
                raise ValueError("supplementary_pdf requires a %PDF- header")
    hash_state = hashlib.sha256()
    byte_count = 0
    with path.open("rb") as handle:
        while True:
            chunk = handle.read(CHUNK_SIZE)
            if not chunk:
                break
            hash_state.update(chunk)
            byte_count += len(chunk)
    actual = hash_state.hexdigest()
    expected = independently_expected_sha256
    if expected is not None:
        expected = expected.strip().lower()
        if len(expected) != 64 or any(c not in "0123456789abcdef" for c in expected):
            raise ValueError("expected sha256 must be exactly 64 hexadecimal digits")
        if actual != expected:
            raise ValueError("provided bytes do not match expected sha256")
    return {
        "schema_version": "dashi.wong2022.local-source-byte-receipt.v1",
        "kind": kind,
        "paper_doi": DOI,
        "paper_canonical_url": SOURCE_URL,
        "local_file_name": path.name,
        "sha256": actual,
        "byte_count": byte_count,
        "container_signature_checked": True,
        "external_expected_digest_matched": expected is not None,
        "publisher_file_identity_authenticated": False,
        "paper_figure_same_object_authenticated": False,
        "underlying_values_analysed": False,
        "chemical_identity_inferred": False,
        "independent_experiment_verification": False,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--source-data", type=Path)
    group.add_argument("--supplement", type=Path)
    parser.add_argument("--expected-sha256")
    args = parser.parse_args()
    kind = "source_data_xlsx" if args.source_data is not None else "supplementary_pdf"
    file_path = args.source_data if args.source_data is not None else args.supplement
    receipt = file_digest_receipt(
        file_path,
        kind=kind,
        independently_expected_sha256=args.expected_sha256,
    )
    print(json.dumps(receipt, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
