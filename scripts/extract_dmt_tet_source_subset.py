#!/usr/bin/env python3
"""Safely extract only the original D'Amelio TET .mat subset from original.zip.

Original experimental dataset/source author: D'Amelio et al. (2026),
doi:10.5281/zenodo.19893951. Not a source reproduction or consent grant.
Runs LOCALLY where the user's original full ZIP and sha256sums.txt exist.
No raw human data is committed into the DASHI repository. Generates a small
subset ZIP for audit when an upload connector has a 256 MiB single-file limit.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
from zipfile import ZipFile, ZipInfo, ZIP_DEFLATED
import stat

MAX_TET_UNCOMPRESSED = 180 * 1024 * 1024
MAX_SINGLE_MEMBER = 32 * 1024 * 1024
MAX_MEMBERS = 500


def expected_hash(sums_path, basename):
    rows = {}
    for line in Path(sums_path).read_text().splitlines():
        parts = line.split(maxsplit=1)
        if len(parts) != 2:
            raise ValueError("Invalid sha256sums record")
        digest, name = parts
        if len(digest) != 64 or any(c not in "0123456789abcdef" for c in digest):
            raise ValueError("Invalid SHA-256 syntax")
        name = name.lstrip("*")
        if name in rows:
            raise ValueError("Ambiguous checksum basename")
        rows[name] = digest
    if basename not in rows:
        raise ValueError("No original ZIP SHA-256 in source checksum list")
    return rows[basename]


def checksum(path):
    sha = hashlib.sha256()
    with Path(path).open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            sha.update(block)
    return sha.hexdigest()


def members(archive):
    with ZipFile(archive) as z:
        selected = []
        seen = set()
        for item in z.infolist():
            name = PurePosixPath(item.filename)
            if (item.filename.startswith("/") or "\\" in item.filename
                    or ".." in name.parts or not item.filename
                    or (item.external_attr >> 16) & 0o170000 == stat.S_IFLNK):
                raise ValueError("Untrusted archive member path or symlink")
            if item.is_dir():
                continue
            if item.filename in seen:
                raise ValueError("Duplicate source ZIP member")
            seen.add(item.filename)
            parts = tuple(p.lower() for p in name.parts)
            if len(parts) >= 3 and parts[-3:-1] == ("reports", "resampled") and name.suffix.lower() == ".mat":
                if item.file_size <= 0 or item.file_size > MAX_SINGLE_MEMBER:
                    raise ValueError("Source TET member exceeds declared 32MiB cap")
                selected.append(item)
        if not selected or len(selected) > MAX_MEMBERS:
            raise ValueError("Source TET subset absent or unexpectedly numerous")
        if sum(m.file_size for m in selected) > MAX_TET_UNCOMPRESSED:
            raise ValueError("TET subset exceeds safe 180 MiB cap")
        return sorted(selected, key=lambda item: item.filename)


def prepare(original_zip, sums_path, output=None):
    original_zip = Path(original_zip)
    if original_zip.name != "original.zip":
        raise ValueError("Expected original.zip, not an arbitrary source")
    good = expected_hash(sums_path, original_zip.name)
    got = checksum(original_zip)
    if got != good:
        raise ValueError("Source original.zip SHA-256 mismatch")
    items = members(original_zip)
    receipt = {
        "source_dataset_doi": "10.5281/zenodo.19893951",
        "original_full_zip_sha256_verified": True,
        "full_zip_sha256": got,
        "source_mat_files": len(items),
        "subset_uncompressed_bytes": sum(f.file_size for f in items),
        "file_names": [f.filename for f in items],
        "source_data_reanalysed": False,
        "human_data_ingested_by_model": False,
    }
    if output is not None:
        output = Path(output)
        if output.exists() or output.resolve() == original_zip.resolve():
            raise ValueError("Refuse overwrite of existing ZIP")
        with ZipFile(original_zip) as input_zip, ZipFile(output, "x", compression=ZIP_DEFLATED) as out_zip:
            for item in items:
                # Stream into output to avoid holding sensitive source bytes in RAM.
                with input_zip.open(item) as src, out_zip.open(item.filename, "w", force_zip64=True) as dst:
                    while chunk := src.read(1024 * 1024):
                        dst.write(chunk)
        receipt["output_zip_name"] = output.name
        receipt["output_zip_bytes"] = output.stat().st_size
        receipt["output_zip_sha256"] = checksum(output)
        if receipt["output_zip_bytes"] > 250 * 1024 * 1024:
            output.unlink()
            raise ValueError("Subset still >250MiB; output discarded")
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("original_zip", type=Path)
    parser.add_argument("sha256sums", type=Path)
    parser.add_argument("--output", type=Path, help="Opt-in small TET-only ZIP")
    a = parser.parse_args()
    print(json.dumps(prepare(a.original_zip, a.sha256sums, a.output),
                     indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
