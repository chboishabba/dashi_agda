#!/usr/bin/env python3
"""Bounded Digital-ESD full-text retrieval transport.

Application-side transport only.  Core review/evidence semantics remain in SLR.

Input:
  fulltext-retrieval-residual.jsonl

For each retained source, try candidate URLs in order.  Successful responses are
stored in a content-addressed cache and written to a retrieved-artifacts manifest
compatible with the existing Digital-ESD full-text gate.

This tool does NOT:
  - decide screening;
  - infer source truth;
  - create reviewed evidence;
  - create SourceAuditAdmission.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import mimetypes
import os
import time
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path
from typing import Any

UA = "DASHI-Digital-ESD/1.0 (+application retrieval wrapper)"
ALLOWED_TYPES = {
    "application/pdf": ".pdf",
    "application/vnd.openxmlformats-officedocument.wordprocessingml.document": ".docx",
    "text/html": ".html",
    "text/plain": ".txt",
    "application/xhtml+xml": ".html",
}


def official_eric_fulltext_url(source_identity_reference: str) -> str | None:
    """Return ERIC's canonical public full-text URL when the ID is usable.

    A reviewed retrieval seed can legitimately carry only its stable ERIC
    identity.  That is enough to nominate ERIC's public file endpoint, but it
    is not evidence that a file exists there: a 404 remains a recorded
    retrieval residual.
    """
    prefix, separator, identifier = source_identity_reference.partition(":")
    if prefix != "ERIC" or separator != ":":
        return None
    identifier = identifier.strip().upper()
    if len(identifier) < 3 or identifier[:2] not in {"EJ", "ED"}:
        return None
    if not identifier[2:].isdigit():
        return None
    return f"https://files.eric.ed.gov/fulltext/{identifier}.pdf"


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as fh:
        for n, line in enumerate(fh, 1):
            if not line.strip():
                continue
            row = json.loads(line)
            if not isinstance(row, dict):
                raise ValueError(f"{path}:{n}: expected object")
            out.append(row)
    return out


def write_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as fh:
        for row in rows:
            fh.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")


def choose_extension(url: str, content_type: str) -> str:
    base = content_type.split(";", 1)[0].strip().lower()
    if base in ALLOWED_TYPES:
        return ALLOWED_TYPES[base]
    suffix = Path(urllib.parse.urlparse(url).path).suffix.lower()
    if suffix in {".pdf", ".docx", ".html", ".htm", ".txt"}:
        return ".html" if suffix == ".htm" else suffix
    guessed = mimetypes.guess_extension(base) if base else None
    return guessed or ".bin"


def download(
    url: str,
    *,
    timeout: float,
    max_bytes: int,
) -> tuple[bytes, str, str]:
    req = urllib.request.Request(
        url,
        headers={
            "User-Agent": UA,
            "Accept": "application/pdf,application/vnd.openxmlformats-officedocument.wordprocessingml.document,text/html,text/plain;q=0.9,*/*;q=0.5",
        },
    )
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        final_url = resp.geturl()
        content_type = str(resp.headers.get("Content-Type") or "")
        declared = resp.headers.get("Content-Length")
        if declared:
            try:
                if int(declared) > max_bytes:
                    raise RuntimeError(
                        f"declared content length {declared} exceeds max {max_bytes}"
                    )
            except ValueError:
                pass

        chunks: list[bytes] = []
        total = 0
        while True:
            chunk = resp.read(min(1024 * 1024, max_bytes - total + 1))
            if not chunk:
                break
            total += len(chunk)
            if total > max_bytes:
                raise RuntimeError(f"response exceeds max {max_bytes} bytes")
            chunks.append(chunk)
        return b"".join(chunks), final_url, content_type


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--residual", type=Path, required=True)
    ap.add_argument("--cache-dir", type=Path, required=True)
    ap.add_argument("--output-manifest", type=Path, required=True)
    ap.add_argument("--failure-log", type=Path)
    ap.add_argument("--max-items", type=int, default=20)
    ap.add_argument("--timeout", type=float, default=30.0)
    ap.add_argument("--max-bytes", type=int, default=100 * 1024 * 1024)
    ap.add_argument("--sleep", type=float, default=0.25)
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    if args.max_items < 1:
        raise ValueError("--max-items must be >= 1")
    if args.max_bytes < 1:
        raise ValueError("--max-bytes must be >= 1")

    rows = read_jsonl(args.residual)
    selected = rows[: args.max_items]
    args.cache_dir.mkdir(parents=True, exist_ok=True)

    successes: list[dict[str, Any]] = []
    failures: list[dict[str, Any]] = []

    for row in selected:
        ref = str(row.get("source_identity_reference") or "").strip()
        if not ref:
            failures.append({"reason": "blank-source-identity", "row": row})
            continue
        urls = [str(u).strip() for u in row.get("candidate_urls", []) if str(u).strip()]
        eric_url = official_eric_fulltext_url(ref)
        if eric_url and eric_url not in urls:
            urls.append(eric_url)
        if not urls:
            failures.append({
                "source_identity_reference": ref,
                "reason": "no-candidate-url",
            })
            continue

        if args.dry_run:
            failures.append({
                "source_identity_reference": ref,
                "reason": "dry-run-not-downloaded",
                "candidate_urls": urls,
            })
            continue

        errors: list[dict[str, str]] = []
        done = False
        for url in urls:
            try:
                data, final_url, content_type = download(
                    url,
                    timeout=args.timeout,
                    max_bytes=args.max_bytes,
                )
                if not data:
                    raise RuntimeError("empty response")
                digest = sha256_bytes(data)
                ext = choose_extension(final_url, content_type)
                artifact = args.cache_dir / digest[:2] / f"{digest}{ext}"
                artifact.parent.mkdir(parents=True, exist_ok=True)
                if not artifact.exists():
                    artifact.write_bytes(data)
                elif artifact.read_bytes() != data:
                    raise RuntimeError("content-addressed cache collision")

                successes.append({
                    "schema": "digital-esd-retrieved-artifact-v1",
                    "source_identity_reference": ref,
                    "artifact_path": str(artifact.resolve()),
                    "sha256": digest,
                    "retrieval_reference": f"http-retrieval:{digest}",
                    "retrieval_timestamp": time.strftime(
                        "%Y-%m-%dT%H:%M:%SZ", time.gmtime()
                    ),
                    "manifestation_family": (
                        "pdf_document" if ext == ".pdf" else "scholarly_full_text"
                    ),
                    "source_url": url,
                    "final_url": final_url,
                    "content_type": content_type,
                    "artifact_bytes": len(data),
                    "candidate_only": True,
                    "creates_source_truth": False,
                    "creates_reviewed_evidence": False,
                    "creates_source_audit_admission": False,
                })
                done = True
                break
            except (urllib.error.URLError, urllib.error.HTTPError, TimeoutError, RuntimeError, OSError) as exc:
                errors.append({"url": url, "error": str(exc)})
        if not done:
            failures.append({
                "source_identity_reference": ref,
                "reason": "all-candidate-urls-failed",
                "errors": errors,
            })
        time.sleep(args.sleep)

    write_jsonl(args.output_manifest, successes)
    if args.failure_log:
        write_jsonl(args.failure_log, failures)

    manifest = {
        "schema": "digital-esd-fulltext-retrieval-run-v1",
        "residual_reference": str(args.residual.resolve()),
        "selected_count": len(selected),
        "downloaded_count": len(successes),
        "failed_or_unresolved_count": len(failures),
        "retrieved_manifest_reference": str(args.output_manifest.resolve()),
        "retrieved_manifest_sha256": hashlib.sha256(
            args.output_manifest.read_bytes()
        ).hexdigest(),
        "candidate_only": True,
        "retrieval_creates_screening_decision": False,
        "retrieval_creates_source_truth": False,
        "retrieval_creates_reviewed_evidence": False,
        "retrieval_creates_source_audit_admission": False,
    }
    print(json.dumps(manifest, indent=2, sort_keys=True))
    return 0 if not failures else 2


if __name__ == "__main__":
    raise SystemExit(main())
