#!/usr/bin/env python3
"""Execute the frozen Digital-ESD ERIC queries and retain lossless raw exports.

The canonical query strings are parsed directly from
DASHI/Education/DigitalESDDatabaseTranslatedQueriesExact.agda so this runner
cannot silently drift from the formal query owner.

Outputs per query:
  <out>/<QID>/page-000000.json ...
  <out>/<QID>/summary.json

summary.json retains the canonical unencoded query, request parameters,
numFound, fetched document count, UTC execution timestamps, page paths and
SHA-256 digests. This script performs execution/export work only. It does not
deduplicate, screen, admit studies, or alter Agda receipts automatically.
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import pathlib
import re
import time
import urllib.parse
import urllib.request
from datetime import datetime, timezone

QUERY_OWNER = pathlib.Path(
    "DASHI/Education/DigitalESDDatabaseTranslatedQueriesExact.agda"
)
ERIC_ENDPOINT = "https://api.ies.ed.gov/eric/"
QUERY_NAMES = {
    "Q1": "ericQ1DigitalEducationESD",
    "Q2": "ericQ2Transformation",
    "Q3": "ericQ3ReflexiveSustainability",
    "Q4": "ericQ4LifecycleCircularity",
    "Q5": "ericQ5ParticipantGovernance",
    "Q6": "ericQ6LongitudinalInstitutional",
    "Q7": "ericQ7OpenInteroperableRepairable",
}


def now_iso() -> str:
    return datetime.now(timezone.utc).astimezone().isoformat(timespec="seconds")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def extract_query(owner_text: str, agda_name: str) -> str:
    pattern = re.compile(
        rf"(?ms)^{re.escape(agda_name)}\s*:\s*TranslatedQueryReceipt.*?"
        rf"Syntax\.ericSyntaxReceipt\s*\n\s*(\"(?:[^\"\\\\]|\\\\.)*\")"
    )
    match = pattern.search(owner_text)
    if not match:
        raise RuntimeError(f"Could not locate exact ERIC query for {agda_name}")
    # Agda string escaping used here is compatible with Python's ordinary
    # quoted-string escapes for the frozen query text.
    return ast.literal_eval(match.group(1))


def load_queries(repo_root: pathlib.Path) -> dict[str, str]:
    owner = repo_root / QUERY_OWNER
    text = owner.read_text(encoding="utf-8")
    return {qid: extract_query(text, name) for qid, name in QUERY_NAMES.items()}


def request_page(query: str, start: int, rows: int, timeout: float) -> tuple[bytes, str]:
    params = {
        "search": query,
        "rows": rows,
        "format": "json",
        "start": start,
    }
    url = ERIC_ENDPOINT + "?" + urllib.parse.urlencode(params)
    req = urllib.request.Request(
        url,
        headers={"User-Agent": "Mozilla/5.0 (compatible; DASHI-Digital-ESD/1.0)"},
    )
    with urllib.request.urlopen(req, timeout=timeout) as response:
        return response.read(), url


def execute_query(
    qid: str,
    query: str,
    out_root: pathlib.Path,
    rows: int,
    timeout: float,
    sleep_seconds: float,
) -> dict:
    qdir = out_root / qid
    qdir.mkdir(parents=True, exist_ok=True)

    started = now_iso()
    start = 0
    page_index = 0
    fetched = 0
    num_found = None
    pages = []

    while num_found is None or fetched < num_found:
        raw, url = request_page(query, start=start, rows=rows, timeout=timeout)
        digest = sha256_bytes(raw)
        page_path = qdir / f"page-{page_index:06d}.json"
        page_path.write_bytes(raw)

        payload = json.loads(raw.decode("utf-8"))
        response = payload.get("response", {})
        docs = response.get("docs", [])
        observed_num_found = response.get("numFound")
        if not isinstance(observed_num_found, int):
            raise RuntimeError(f"{qid}: ERIC response missing integer numFound")
        if num_found is None:
            num_found = observed_num_found
        elif observed_num_found != num_found:
            raise RuntimeError(
                f"{qid}: numFound changed during pagination "
                f"({num_found} -> {observed_num_found})"
            )

        pages.append(
            {
                "page_index": page_index,
                "start": start,
                "rows_requested": rows,
                "docs_returned": len(docs),
                "request_url": url,
                "path": str(page_path),
                "sha256": digest,
            }
        )
        fetched += len(docs)

        if not docs:
            break

        start += len(docs)
        page_index += 1
        if fetched < num_found:
            time.sleep(sleep_seconds)

    completed = now_iso()
    complete = num_found is not None and fetched >= num_found

    summary = {
        "query_id": qid,
        "agda_query_name": QUERY_NAMES[qid],
        "canonical_unencoded_query": query,
        "endpoint": ERIC_ENDPOINT,
        "format": "json",
        "rows_requested": rows,
        "execution_started": started,
        "execution_completed": completed,
        "numFound": num_found,
        "fetched_docs": fetched,
        "pagination_complete": complete,
        "pages": pages,
        "promotion_boundary": (
            "execution/export receipt only; does not deduplicate, screen, "
            "create SourceAuditAdmission, or create CorpusAuditedSource"
        ),
    }
    summary_bytes = (
        json.dumps(summary, indent=2, ensure_ascii=False, sort_keys=True) + "\n"
    ).encode("utf-8")
    summary["summary_sha256_without_self_field"] = sha256_bytes(summary_bytes)
    summary_path = qdir / "summary.json"
    summary_path.write_text(
        json.dumps(summary, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return summary


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", default=".")
    parser.add_argument(
        "--out",
        default="artifacts/digital-esd/eric",
        help="output directory relative to repo root unless absolute",
    )
    parser.add_argument(
        "--query",
        action="append",
        choices=sorted(QUERY_NAMES),
        help="execute only selected QID; repeatable. Default: Q1-Q7",
    )
    parser.add_argument("--rows", type=int, default=200)
    parser.add_argument("--timeout", type=float, default=30.0)
    parser.add_argument("--sleep", type=float, default=0.25)
    args = parser.parse_args()

    if args.rows < 1 or args.rows > 200:
        raise SystemExit("--rows must be in [1, 200]")

    repo_root = pathlib.Path(args.repo_root).resolve()
    out_root = pathlib.Path(args.out)
    if not out_root.is_absolute():
        out_root = repo_root / out_root
    out_root.mkdir(parents=True, exist_ok=True)

    queries = load_queries(repo_root)
    selected = args.query or list(QUERY_NAMES)

    run_manifest = {
        "runner": "scripts/execute_digital_esd_eric.py",
        "repo_root": str(repo_root),
        "started": now_iso(),
        "query_ids": selected,
        "results": [],
    }

    for qid in selected:
        result = execute_query(
            qid=qid,
            query=queries[qid],
            out_root=out_root,
            rows=args.rows,
            timeout=args.timeout,
            sleep_seconds=args.sleep,
        )
        run_manifest["results"].append(result)
        print(
            f"{qid}: numFound={result['numFound']} "
            f"fetched={result['fetched_docs']} "
            f"complete={result['pagination_complete']}"
        )

    run_manifest["completed"] = now_iso()
    manifest_path = out_root / "run-manifest.json"
    manifest_path.write_text(
        json.dumps(run_manifest, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(f"manifest: {manifest_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
