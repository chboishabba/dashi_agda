#!/usr/bin/env python3
"""Normalize retained ERIC records into stable Digital-ESD study-metadata rows.

This is real parsing of the ERIC bibliographic records (title, abstract,
authors, identifiers, descriptors, publication metadata, links and query
provenance). It is NOT full-text paper parsing.

The raw input record is never discarded semantically: every normalized row
retains the exact source-record SHA-256 so it can be welded back to the
deduplicated export.

Authority boundary:
  metadata parse != screening decision
  abstract parse != full-text study analysis
  bibliographic field != empirical truth
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from typing import Any

PARSER_ID = "digital-esd-eric-record-normalizer-v1"
DOI_RE = re.compile(r"10\.\d{4,9}/[-._;()/:a-z0-9]+", re.I)
YEAR_RE = re.compile(r"(?:19|20)\d{2}")
URL_RE = re.compile(r"https?://[^\s<>\"']+")


def canonical_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
        + "\n"
    ).encode("utf-8")


def sha256_json(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def load_rows(path: Path) -> list[dict[str, Any]]:
    text = path.read_text(encoding="utf-8")
    if path.suffix.lower() == ".jsonl":
        rows: list[dict[str, Any]] = []
        for line_no, line in enumerate(text.splitlines(), 1):
            if not line.strip():
                continue
            row = json.loads(line)
            if not isinstance(row, dict):
                raise ValueError(f"{path}:{line_no}: expected JSON object")
            rows.append(row)
        return rows

    payload = json.loads(text)
    if isinstance(payload, list):
        rows = payload
    elif isinstance(payload, dict):
        rows = next(
            (
                payload[key]
                for key in ("records", "items", "docs", "results")
                if isinstance(payload.get(key), list)
            ),
            None,
        )
        if rows is None:
            raise ValueError(
                "JSON object must contain records/items/docs/results array"
            )
    else:
        raise ValueError("input must be JSON array/JSONL/object containing rows")

    if not all(isinstance(row, dict) for row in rows):
        raise ValueError("every ERIC record must be an object")
    return list(rows)


def value(row: dict[str, Any], *keys: str) -> Any:
    for key in keys:
        if key in row and row[key] not in (None, "", []):
            return row[key]
    return None


def text(row: dict[str, Any], *keys: str) -> str:
    v = value(row, *keys)
    if isinstance(v, str):
        return " ".join(v.split()).strip()
    if isinstance(v, (int, float)):
        return str(v)
    if isinstance(v, list):
        return "; ".join(str(x).strip() for x in v if str(x).strip())
    return ""


def list_value(row: dict[str, Any], *keys: str) -> list[str]:
    v = value(row, *keys)
    if v is None:
        return []
    if isinstance(v, list):
        items = [str(x).strip() for x in v if str(x).strip()]
    else:
        raw = str(v)
        # ERIC exports commonly use semicolons for multi-valued metadata.
        items = [part.strip() for part in re.split(r";|\|", raw) if part.strip()]
    out: list[str] = []
    seen: set[str] = set()
    for item in items:
        if item not in seen:
            seen.add(item)
            out.append(item)
    return out


def doi(row: dict[str, Any]) -> str | None:
    explicit = text(row, "DOI", "doi")
    if explicit:
        match = DOI_RE.search(explicit)
        return (
            match.group(0).lower().rstrip(".,;)")
            if match
            else explicit.lower().strip()
        )
    haystack = " ".join(
        str(v) for v in row.values() if isinstance(v, (str, int, float))
    )
    match = DOI_RE.search(haystack)
    return match.group(0).lower().rstrip(".,;)") if match else None


def eric_id(row: dict[str, Any]) -> str | None:
    raw = text(row, "ID", "id", "ERICNumber", "eric_id", "ericId")
    return raw or None


def source_identity(row: dict[str, Any]) -> str:
    eid = eric_id(row)
    if eid:
        return f"ERIC:{eid}"
    d = doi(row)
    if d:
        return f"DOI:{d}"
    fallback = {
        "title": text(row, "Title", "title"),
        "authors": list_value(row, "Author", "Authors", "author", "authors"),
        "date": text(row, "PublicationDate", "publication_date", "Year", "year"),
        "raw_sha256": sha256_json(row),
    }
    return "METADATA:" + sha256_json(fallback)


def year(row: dict[str, Any]) -> int | None:
    raw = text(row, "PublicationDate", "publication_date", "Year", "year")
    match = YEAR_RE.search(raw)
    return int(match.group(0)) if match else None


def urls(row: dict[str, Any]) -> list[str]:
    candidates: list[str] = []
    for key in (
        "URL",
        "url",
        "FullTextURL",
        "full_text_url",
        "DownloadURL",
        "download_url",
        "Identifiers",
        "identifiers",
    ):
        v = value(row, key)
        if isinstance(v, str):
            candidates.extend(URL_RE.findall(v))
        elif isinstance(v, list):
            for item in v:
                candidates.extend(URL_RE.findall(str(item)))
    out: list[str] = []
    seen: set[str] = set()
    for candidate in candidates:
        candidate = candidate.rstrip(".,;)")
        if candidate not in seen:
            seen.add(candidate)
            out.append(candidate)
    return out


def query_membership(row: dict[str, Any]) -> list[str]:
    raw = value(
        row,
        "query_ids",
        "query_membership",
        "query_memberships",
        "queries",
        "source_queries",
        "matched_queries",
    )
    if raw is None:
        return []
    if isinstance(raw, list):
        return sorted({str(x) for x in raw})
    return sorted({x.strip() for x in re.split(r"[,;|]", str(raw)) if x.strip()})


def normalize(row: dict[str, Any]) -> dict[str, Any]:
    raw_sha = sha256_json(row)
    title = text(row, "Title", "title")
    abstract = text(
        row,
        "Description",
        "description",
        "Abstract",
        "abstract",
        "Summary",
        "summary",
    )
    parsed = {
        "schema": "digital-esd-eric-study-metadata-v1",
        "parser_reference": PARSER_ID,
        "source_identity_reference": source_identity(row),
        "eric_id": eric_id(row),
        "doi": doi(row),
        "title": title,
        "abstract": abstract,
        "authors": list_value(row, "Author", "Authors", "author", "authors"),
        "year": year(row),
        "publication_date": text(
            row, "PublicationDate", "publication_date", "Date", "date"
        )
        or None,
        "publication_type": list_value(
            row,
            "PublicationType",
            "publication_type",
            "publication_types",
            "DocumentType",
        ),
        "subjects": list_value(
            row, "Subject", "subject", "subjects", "Descriptors", "descriptors"
        ),
        "education_level": list_value(
            row, "EducationLevel", "education_level", "education_levels"
        ),
        "audience": list_value(row, "Audience", "audience"),
        "language": list_value(row, "Language", "language"),
        "peer_reviewed": value(row, "PeerReviewed", "peer_reviewed"),
        "journal_or_source": text(
            row,
            "Journal",
            "journal",
            "Source",
            "source",
            "Publication",
            "publication",
        )
        or None,
        "institution": list_value(
            row, "Institution", "institution", "InstitutionName"
        ),
        "isbn": list_value(row, "ISBN", "isbn"),
        "issn": list_value(row, "ISSN", "issn"),
        "fulltext_or_record_urls": urls(row),
        "query_membership": query_membership(row),
        "raw_metadata_sha256": raw_sha,
        "has_title": bool(title),
        "has_abstract": bool(abstract),
        "candidate_only": True,
        "parse_creates_screening_decision": False,
        "parse_creates_source_truth": False,
        "parse_is_fulltext_study_analysis": False,
    }
    parsed["parsed_record_sha256"] = sha256_json(parsed)
    return parsed


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", required=True, type=Path)
    ap.add_argument(
        "--out",
        type=Path,
        default=Path(
            "artifacts/digital-esd/parsed/eric-parsed-studies.jsonl"
        ),
    )
    ap.add_argument("--expected-count", type=int)
    args = ap.parse_args()

    rows = load_rows(args.input)
    parsed = [normalize(row) for row in rows]

    identities = [row["source_identity_reference"] for row in parsed]
    if len(set(identities)) != len(identities):
        duplicates = [
            identity
            for identity in sorted(set(identities))
            if identities.count(identity) > 1
        ]
        raise RuntimeError(
            "normalized ERIC input still contains duplicate stable identities: "
            + ", ".join(duplicates[:20])
        )

    if args.expected_count is not None and len(parsed) != args.expected_count:
        raise RuntimeError(
            f"record count mismatch: expected={args.expected_count} "
            f"observed={len(parsed)}"
        )

    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("w", encoding="utf-8") as fh:
        for row in parsed:
            fh.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")

    manifest = {
        "schema": "digital-esd-eric-study-metadata-manifest-v1",
        "parser_reference": PARSER_ID,
        "input_reference": str(args.input),
        "input_sha256": hashlib.sha256(args.input.read_bytes()).hexdigest(),
        "output_reference": str(args.out),
        "output_sha256": hashlib.sha256(args.out.read_bytes()).hexdigest(),
        "record_count": len(parsed),
        "with_title": sum(bool(row["has_title"]) for row in parsed),
        "with_abstract": sum(bool(row["has_abstract"]) for row in parsed),
        "with_doi": sum(bool(row["doi"]) for row in parsed),
        "with_fulltext_or_record_url": sum(
            bool(row["fulltext_or_record_urls"]) for row in parsed
        ),
        "parse_creates_screening_decision": False,
        "parse_is_fulltext_study_analysis": False,
    }
    manifest_path = args.out.with_name("eric-parsed-studies-manifest.json")
    manifest_path.write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(manifest, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
