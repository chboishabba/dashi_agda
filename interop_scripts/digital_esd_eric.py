#!/usr/bin/env python3
"""Parse retained ERIC API exports into real Digital-ESD study-metadata records.

This is the missing bridge between raw ERIC API pages and the authoritative
Digital-ESD screening ledger.  It parses *real ERIC records*, not the synthetic
43,996-row SLR scale fixture.

Expected export layout (produced by scripts/execute_digital_esd_eric.py):

  <export-root>/
    Q1/
      page-000000.json
      ...
      summary.json
    ...
    Q7/
      ...
    run-manifest.json

The parser verifies every page against the retained summary SHA-256, checks
pagination/count completeness, normalizes the documented ERIC fields, and
deduplicates only by stable ERIC id while retaining every query membership.

Important authority boundaries:

  ERIC metadata parsed       != title/abstract screening decision
  abstract parsed            != full paper parsed
  ERIC full-text availability != full text retrieved
  metadata similarity        != same empirical study
  parsed record              != SourceAuditAdmission
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import defaultdict
from pathlib import Path
from typing import Any


PARSER_VERSION = "digital-esd-eric-parser-v1"
DEFAULT_QUERY_IDS = tuple(f"Q{i}" for i in range(1, 8))


def canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
        + "\n"
    ).encode("utf-8")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def as_text(value: Any) -> str:
    if isinstance(value, str):
        return " ".join(value.split()).strip()
    if value is None:
        return ""
    return " ".join(str(value).split()).strip()


def as_text_list(value: Any) -> list[str]:
    if value is None:
        return []
    if isinstance(value, list):
        out = [as_text(item) for item in value]
    elif isinstance(value, tuple):
        out = [as_text(item) for item in value]
    else:
        out = [as_text(value)]
    return [item for item in out if item]


def first_present(doc: dict[str, Any], *keys: str) -> Any:
    for key in keys:
        if key in doc and doc[key] not in (None, "", []):
            return doc[key]
    return None


def normalize_eric_id(value: Any) -> str:
    eric_id = as_text(value)
    if not eric_id:
        raise ValueError("ERIC document missing id")
    return eric_id.upper()


def normalized_record(doc: dict[str, Any]) -> dict[str, Any]:
    """Normalize only documented/source-bounded ERIC bibliographic fields."""

    eric_id = normalize_eric_id(first_present(doc, "id", "ID"))

    title = as_text(first_present(doc, "title", "Title"))
    description = as_text(
        first_present(doc, "description", "Description", "abstract", "Abstract")
    )

    record = {
        "eric_id": eric_id,
        "source_identity_reference": f"ERIC:{eric_id}",
        "title": title,
        "abstract": description,
        "authors": as_text_list(first_present(doc, "author", "Author")),
        "source": as_text(first_present(doc, "source", "Source")),
        "publication_date_year": as_text(
            first_present(doc, "publicationdateyear", "PublicationDateYear")
        ),
        "subjects": as_text_list(first_present(doc, "subject", "Subject")),
        "education_levels": as_text_list(
            first_present(doc, "educationlevel", "EducationLevel")
        ),
        "publication_types": as_text_list(
            first_present(doc, "publicationtype", "PublicationType")
        ),
        "institutions": as_text_list(
            first_present(doc, "institution", "Institution")
        ),
        "publisher": as_text(first_present(doc, "publisher", "Publisher")),
        "sponsors": as_text_list(first_present(doc, "sponsor", "Sponsor")),
        "languages": as_text_list(first_present(doc, "language", "Language")),
        "audiences": as_text_list(first_present(doc, "audience", "Audience")),
        "peer_reviewed": first_present(doc, "peerreviewed", "PeerReviewed"),
        "url": as_text(first_present(doc, "url", "URL")),
        "isbn": as_text_list(first_present(doc, "isbn", "ISBN")),
        "issn": as_text_list(first_present(doc, "issn", "ISSN")),
        "source_id": as_text(first_present(doc, "sourceid", "SourceID")),
        "full_text_authorized_metadata": first_present(
            doc, "efulltextauth", "e fulltextauth", "EFullTextAuth"
        ),
        "ies_link_publication": as_text(
            first_present(doc, "ieslinkpublication", "IESLinkPublication")
        ),
        "identifiers_geo": as_text_list(
            first_present(doc, "identifiersgeo", "IdentifiersGeo")
        ),
        "identifiers_law": as_text_list(
            first_present(doc, "identifierslaw", "IdentifiersLaw")
        ),
        "identifiers_test": as_text_list(
            first_present(doc, "identifierstest", "IdentifiersTest")
        ),
        "abstract_present": bool(description),
        # Deliberately false here. Parsing metadata/abstract is not parsing paper text.
        "full_text_parsed": False,
        "full_text_retrieved": False,
        "creates_screening_decision": False,
        "creates_source_truth": False,
        "creates_source_audit_admission": False,
    }

    # Metadata revision is a digest of normalized ERIC fields, not query membership.
    revision_basis = {
        key: value
        for key, value in record.items()
        if key
        not in {
            "source_identity_reference",
            "creates_screening_decision",
            "creates_source_truth",
            "creates_source_audit_admission",
            "full_text_parsed",
            "full_text_retrieved",
        }
    }
    metadata_sha = sha256_bytes(canonical_json_bytes(revision_basis))
    record["metadata_sha256"] = metadata_sha
    record["metadata_revision_reference"] = f"eric-metadata-sha256:{metadata_sha}"
    return record


def load_summary(qdir: Path, qid: str) -> dict[str, Any]:
    path = qdir / "summary.json"
    if not path.exists():
        raise FileNotFoundError(f"{qid}: missing {path}")
    summary = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(summary, dict):
        raise ValueError(f"{qid}: summary is not an object")
    if summary.get("query_id") not in (None, qid):
        raise ValueError(
            f"{qid}: summary query_id mismatch: {summary.get('query_id')!r}"
        )
    if summary.get("pagination_complete") is not True:
        raise ValueError(f"{qid}: pagination_complete is not true")
    return summary


def verified_docs_for_query(
    export_root: Path, qid: str
) -> tuple[list[tuple[dict[str, Any], dict[str, Any]]], dict[str, Any]]:
    qdir = export_root / qid
    summary = load_summary(qdir, qid)
    pages = summary.get("pages")
    if not isinstance(pages, list) or not pages:
        raise ValueError(f"{qid}: summary has no pages")

    docs_with_provenance: list[tuple[dict[str, Any], dict[str, Any]]] = []
    expected_start = 0

    for page in pages:
        if not isinstance(page, dict):
            raise ValueError(f"{qid}: malformed page receipt")
        page_path_raw = page.get("path")
        if not isinstance(page_path_raw, str) or not page_path_raw:
            raise ValueError(f"{qid}: page receipt missing path")

        page_path = Path(page_path_raw)
        if not page_path.is_absolute():
            # The executor may have retained either paths rooted from cwd or qdir.
            if (export_root / page_path).exists():
                page_path = export_root / page_path
            elif (qdir / page_path.name).exists():
                page_path = qdir / page_path.name
            else:
                page_path = qdir / page_path

        raw = page_path.read_bytes()
        observed_sha = sha256_bytes(raw)
        expected_sha = as_text(page.get("sha256")).lower()
        if expected_sha and observed_sha != expected_sha:
            raise ValueError(
                f"{qid}: page digest mismatch for {page_path}: "
                f"expected={expected_sha} observed={observed_sha}"
            )

        payload = json.loads(raw.decode("utf-8"))
        response = payload.get("response")
        if not isinstance(response, dict):
            raise ValueError(f"{qid}: {page_path} missing response object")
        docs = response.get("docs")
        if not isinstance(docs, list):
            raise ValueError(f"{qid}: {page_path} missing docs array")

        page_start = response.get("start", page.get("start"))
        if isinstance(page_start, int) and page_start != expected_start:
            raise ValueError(
                f"{qid}: pagination discontinuity expected start "
                f"{expected_start}, got {page_start}"
            )

        for local_index, doc in enumerate(docs):
            if not isinstance(doc, dict):
                raise ValueError(
                    f"{qid}: {page_path}: docs[{local_index}] is not an object"
                )
            docs_with_provenance.append(
                (
                    doc,
                    {
                        "query_id": qid,
                        "canonical_unencoded_query": summary.get(
                            "canonical_unencoded_query"
                        ),
                        "page_reference": str(page_path),
                        "page_sha256": observed_sha,
                        "page_index": page.get("page_index"),
                        "page_start": page.get("start"),
                        "doc_index_in_page": local_index,
                        "request_url": page.get("request_url"),
                    },
                )
            )

        expected_start += len(docs)

    observed_count = len(docs_with_provenance)
    fetched_docs = summary.get("fetched_docs")
    num_found = summary.get("numFound")
    if isinstance(fetched_docs, int) and observed_count != fetched_docs:
        raise ValueError(
            f"{qid}: parsed {observed_count} docs but summary fetched_docs="
            f"{fetched_docs}"
        )
    if isinstance(num_found, int) and observed_count < num_found:
        raise ValueError(
            f"{qid}: parsed {observed_count} docs but numFound={num_found}"
        )

    return docs_with_provenance, summary


def parse_exports(
    export_root: Path, query_ids: tuple[str, ...]
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    by_id: dict[str, dict[str, Any]] = {}
    membership: dict[str, set[str]] = defaultdict(set)
    provenance: dict[str, list[dict[str, Any]]] = defaultdict(list)
    query_summaries: dict[str, dict[str, Any]] = {}
    raw_occurrences = 0

    for qid in query_ids:
        docs, summary = verified_docs_for_query(export_root, qid)
        query_summaries[qid] = {
            "numFound": summary.get("numFound"),
            "fetched_docs": summary.get("fetched_docs"),
            "pagination_complete": summary.get("pagination_complete"),
            "summary_reference": str(export_root / qid / "summary.json"),
            "summary_sha256": sha256_file(export_root / qid / "summary.json"),
        }

        for raw_doc, raw_provenance in docs:
            raw_occurrences += 1
            normalized = normalized_record(raw_doc)
            eric_id = normalized["eric_id"]

            previous = by_id.get(eric_id)
            if previous is None:
                by_id[eric_id] = normalized
            elif previous["metadata_sha256"] != normalized["metadata_sha256"]:
                raise ValueError(
                    "conflicting normalized metadata for stable ERIC id "
                    f"{eric_id}: {previous['metadata_revision_reference']} vs "
                    f"{normalized['metadata_revision_reference']}"
                )

            membership[eric_id].add(qid)
            provenance[eric_id].append(raw_provenance)

    records: list[dict[str, Any]] = []
    for eric_id in sorted(by_id):
        row = dict(by_id[eric_id])
        row["query_memberships"] = sorted(membership[eric_id])
        row["raw_observation_count"] = len(provenance[eric_id])
        row["raw_observations"] = provenance[eric_id]
        records.append(row)

    manifest = {
        "schema": "digital-esd-eric-study-metadata-manifest-v1",
        "parser_version": PARSER_VERSION,
        "export_root": str(export_root),
        "query_ids": list(query_ids),
        "query_summaries": query_summaries,
        "raw_query_occurrence_count": raw_occurrences,
        "unique_eric_record_count": len(records),
        "records_with_abstract": sum(1 for row in records if row["abstract_present"]),
        "records_without_abstract": sum(
            1 for row in records if not row["abstract_present"]
        ),
        "records_with_full_text_parsed": 0,
        "parsed_metadata_creates_screening_decision": False,
        "parsed_metadata_creates_source_truth": False,
        "parsed_metadata_creates_source_audit_admission": False,
    }
    return records, manifest


def write_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(
                json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n"
            )


def cmd_parse(args: argparse.Namespace) -> int:
    query_ids = tuple(args.query or DEFAULT_QUERY_IDS)
    records, manifest = parse_exports(args.export_root, query_ids)

    if args.expect_occurrences is not None:
        if manifest["raw_query_occurrence_count"] != args.expect_occurrences:
            raise ValueError(
                "raw occurrence count mismatch: expected "
                f"{args.expect_occurrences}, observed "
                f"{manifest['raw_query_occurrence_count']}"
            )
    if args.expect_unique is not None:
        if manifest["unique_eric_record_count"] != args.expect_unique:
            raise ValueError(
                "unique ERIC count mismatch: expected "
                f"{args.expect_unique}, observed "
                f"{manifest['unique_eric_record_count']}"
            )

    write_jsonl(args.output, records)
    manifest["output_reference"] = str(args.output)
    manifest["output_sha256"] = sha256_file(args.output)

    manifest_path = args.manifest or args.output.with_suffix(".manifest.json")
    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    manifest_path.write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(manifest, sort_keys=True))
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command_name", required=True)

    parse = sub.add_parser("parse")
    parse.add_argument("--export-root", required=True, type=Path)
    parse.add_argument("--output", required=True, type=Path)
    parse.add_argument("--manifest", type=Path)
    parse.add_argument(
        "--query",
        action="append",
        choices=DEFAULT_QUERY_IDS,
        help="query id to parse; repeatable; defaults to Q1-Q7",
    )
    parse.add_argument("--expect-occurrences", type=int)
    parse.add_argument("--expect-unique", type=int)
    parse.set_defaults(func=cmd_parse)
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
