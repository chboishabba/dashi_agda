#!/usr/bin/env python3
"""Source-first locate/download of ORIGINAL NOAA 1953 Bangor ISD object.

NOAA NCEI owns original meteorological observations and S3 distribution.
This acquisition adapter is by Johl Brown with ChatGPT assistance.

The 2018 legacy file is known, but its 2026 NODD/S3 object KEY is NOT
verified. Query actual public bucket listings; never invent an object key.
Local SHA256 is a checksum of acquired bytes, not an agency-signed receipt.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from pathlib import Path

BUCKET = "https://noaa-isd-pds.s3.amazonaws.com"
TARGET = "726071-14606-1953.gz"
LEGACY = "https://www.ncei.noaa.gov/pub/data/noaa/1953/" + TARGET
MIGRATION = "https://www.nesdis.noaa.gov/news/service-location-change-integrated-surface-data-global-hourly"
PREFIXES = ("1953/", "data/1953/", "isd/1953/", "pub/data/noaa/1953/")
MAX_PAGES = 24
TIMEOUT = 15


def parse_listing(xml_bytes: bytes) -> tuple[list[dict], str | None]:
    """S3 ListObjectsV2 XML, using namespace-independent field names."""
    root = ET.fromstring(xml_bytes)
    tag = lambda s: s.rsplit("}", 1)[-1]
    if tag(root.tag) != "ListBucketResult":
        error_code = next((e.text for e in root.iter() if tag(e.tag) == "Code"), None)
        raise ValueError("S3 did not return an object listing: " + str(error_code))
    objects = []
    for element in root:
        if tag(element.tag) != "Contents":
            continue
        fields = {tag(e.tag): (e.text or "") for e in element}
        if "Key" not in fields or "Size" not in fields:
            raise ValueError("incomplete bucket listing entry")
        objects.append({
            "key": fields["Key"],
            "size": int(fields["Size"]),
            "etag_not_authenticated_sha": fields.get("ETag", ""),
            "modified": fields.get("LastModified", ""),
        })
    is_truncated = next((x.text or "" for x in root if tag(x.tag) == "IsTruncated"), "")
    continuation = next((x.text or "" for x in root if tag(x.tag) == "NextContinuationToken"), "")
    if is_truncated == "true" and not continuation:
        raise ValueError("truncated S3 listing lacks continuation token")
    return objects, continuation if is_truncated == "true" else None


def listing_url(prefix: str, token: str | None = None) -> str:
    query = {"list-type": "2", "prefix": prefix}
    if token:
        query["continuation-token"] = token
    return BUCKET + "/?" + urllib.parse.urlencode(query)


def locate(prefixes: tuple[str, ...] = PREFIXES) -> dict:
    scans, candidates, failures = [], [], []
    for prefix in prefixes:
        seen_tokens = set()
        token = None
        completed = False
        for page in range(MAX_PAGES):
            url = listing_url(prefix, token)
            try:
                with urllib.request.urlopen(url, timeout=TIMEOUT) as response:
                    objects, next_token = parse_listing(response.read())
            except (urllib.error.HTTPError, urllib.error.URLError,
                    OSError, ValueError, ET.ParseError) as exc:
                failures.append({"prefix": prefix, "page": page, "error": str(exc)[:250]})
                break
            scans.append({"prefix": prefix, "page": page, "entries": len(objects)})
            for obj in objects:
                if obj["key"].rsplit("/", 1)[-1] == TARGET:
                    candidates.append(obj)
            if next_token is None:
                completed = True
                break
            if next_token in seen_tokens:
                failures.append({"prefix": prefix, "error": "repeating continuation token"})
                break
            seen_tokens.add(next_token)
            token = next_token
        if not completed and not any(f["prefix"] == prefix for f in failures):
            failures.append({"prefix": prefix, "error": "bounded page budget exhausted"})
    keys = {c["key"]: c for c in candidates}
    return {
        "original_NOAA_custodian": "NOAA/NCEI ISD",
        "agency_legacy_index": LEGACY,
        "original_public_bucket": BUCKET,
        "agency_migration_notice": MIGRATION,
        "actual_listing_matches": list(keys.values()),
        "listing_pages_examined": scans,
        "prefix_failures_or_bounded_gaps": failures,
        "historical_1953_data_read": False,
        "agency_authenticated_original_checksum": False,
    }


def download_exact_key(key: str, path: Path) -> dict:
    """Only a key returned by an actual listing may be passed by main()."""
    if key.rsplit("/", 1)[-1] != TARGET:
        raise ValueError("selected S3 key does not identify expected station-year")
    if path.exists():
        raise FileExistsError("refusing to overwrite existing source file")
    url = BUCKET + "/" + urllib.parse.quote(key, safe="/")
    with urllib.request.urlopen(url, timeout=TIMEOUT) as response:
        blob = response.read()
    if not blob.startswith(b"\x1f\x8b"):
        raise ValueError("download was not a gzip original-format object")
    if not blob:
        raise ValueError("empty downloaded source object")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(blob)
    return {
        "s3_key_observed_from_actual_listing": key,
        "s3_object_url": url,
        "local_saved_path": str(path),
        "received_compressed_bytes": len(blob),
        "local_sha256_not_publisher_authenticated": hashlib.sha256(blob).hexdigest(),
        "is_original_1953_hourly_data_parsed": False,
        "meteorological_causal_effect_verified": False,
    }


def self_test() -> dict:
    xml = b'<ListBucketResult xmlns="http://s3.amazonaws.com/doc/2006-03-01/"><IsTruncated>true</IsTruncated><NextContinuationToken>x&amp;y</NextContinuationToken><Contents><Key>data/1953/726071-14606-1953.gz</Key><Size>160944</Size><ETag>"example"</ETag></Contents></ListBucketResult>'
    rows, token = parse_listing(xml)
    assert len(rows) == 1 and rows[0]["size"] == 160944 and token == "x&y"
    assert "continuation-token=x%26y" in listing_url("data/1953/", token)
    rows2, tok2 = parse_listing(b'<ListBucketResult><IsTruncated>false</IsTruncated></ListBucketResult>')
    assert not rows2 and tok2 is None
    invalid = 0
    for raw in (b"<Error><Code>AccessDenied</Code></Error>",
                b"<ListBucketResult><IsTruncated>true</IsTruncated></ListBucketResult>",
                b"<wrong>"):
        try:
            parse_listing(raw)
        except (ET.ParseError, ValueError):
            invalid += 1
        else:
            raise AssertionError("malformed S3 listing accepted")
    assert invalid == 3
    return {"synthetic_listing_cases_passed": 5, "publisher_object_acquired": False}


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--prefix", action="append", dest="prefixes", help="additional exact S3 prefix to list")
    p.add_argument("--download-to", type=Path, help="save matched gzip only when one unique key was located")
    p.add_argument("--self-test", action="store_true")
    args = p.parse_args()
    if args.self_test and not (args.download_to or args.prefixes):
        print(json.dumps({"self_test": self_test()}, indent=2))
        return
    result = locate(tuple(args.prefixes) if args.prefixes else PREFIXES)
    if args.download_to:
        candidates = result["actual_listing_matches"]
        if len(candidates) != 1:
            raise ValueError("requires one actual original station-year S3 key, found " + str(len(candidates)))
        result["download"] = download_exact_key(candidates[0]["key"], args.download_to)
    if args.self_test:
        result["self_test"] = self_test()
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
