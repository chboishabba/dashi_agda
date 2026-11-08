#!/usr/bin/env python3
"""Fail-closed official GovInfo acquisition and source-byte to candidate PNF spans.

Usage:
  python3 scripts/build_ccdcoe_p3_primary_intake.py --self-test
  python3 scripts/build_ccdcoe_p3_primary_intake.py \
      --fetch-govinfo --archive /archive/record.html \
      --output /archive/candidates.json
  python3 scripts/build_ccdcoe_p3_primary_intake.py \
      --source /archive/record.html --output /archive/candidates.json

The --fetch-govinfo route acquires ONLY the pinned public government HTML;
--source accepts separately obtained bytes. Neither substitutes for semantic
source review, original scanned-image authenticity or native EventPNF admission.
SHA256 covers the raw input BYTES. All character offsets refer explicitly
to normalized extracted text, not raw HTML bytes or Agda SpanReceipt tokens.
"""
from __future__ import annotations
import argparse
import hashlib
from html.parser import HTMLParser
import json
import os
from pathlib import Path
import tempfile
from urllib.request import Request, urlopen
import re
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "Docs/research/ccdcoe_p3_climate_case_manifest.json"
OFFICIAL_URL = ("https://www.govinfo.gov/content/pkg/CREC-1998-04-27/"
                "html/CREC-1998-04-27-pt1-PgH2323.htm")
MAX_SOURCE_BYTES = 8 * 1024 * 1024
ANCHORS: dict[str, str] = {
    "document_circulation":
        "Subject: Draft Global Climate Science Communications Plan",
    "named_contributors":
        "GCSCT members who contributed to the development",
    "public_opinion_objectives":
        "Progress will be measured toward the goal.",
    "media_tactics":
        "I. National Media Relations Program:",
    "science_center_proposal":
        "Establish a Global Climate Science Data Center.",
    "planned_tracking_metrics":
        "Baseline public/government official opinion surveys",
}

class TextExtractor(HTMLParser):
    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.text: list[str] = []
        self.skip = 0

    def handle_starttag(self, tag: str, attrs: list) -> None:
        if tag in ("script", "style"):
            self.skip += 1

    def handle_endtag(self, tag: str) -> None:
        if tag in ("script", "style") and self.skip:
            self.skip -= 1

    def handle_data(self, data: str) -> None:
        if self.skip == 0:
            self.text.append(data)

def extract(raw: bytes) -> str:
    decoded = raw.decode("utf-8", errors="strict")
    parser = TextExtractor()
    parser.feed(decoded)
    return re.sub(r"\s+", " ", " ".join(parser.text)).strip()

def locate_unique(text: str, anchor: str) -> tuple[int, int]:
    locations = [m.span() for m in re.finditer(
        re.escape(anchor), text, flags=re.IGNORECASE)]
    if len(locations) != 1:
        raise ValueError(
            f"Anchor must occur exactly once; found {len(locations)}: {anchor}")
    return locations[0]

def prepare(raw: bytes, manifest: dict[str, Any]) -> dict[str, Any]:
    if b"Global Climate Science" not in raw:
        raise ValueError("Input is not visibly the expected climate record")
    text = extract(raw)
    if not text:
        raise ValueError("Document extraction returned empty text")
    pub = manifest["primary_publication"]
    if pub["url"] != OFFICIAL_URL:
        raise ValueError("Unexpected canonical source locator")
    if len(raw) > MAX_SOURCE_BYTES:
        raise ValueError("Source exceeds bounded size")
    rows = manifest["pnf_candidate_intake"]
    indexed = {row["candidate_id"].removeprefix("pnf-"): row for row in rows}
    if set(indexed) != set(ANCHORS):
        raise ValueError("Manifest candidate identities do not match anchors")
    resolved = []
    previous_end = -1
    for claim_id, anchor in ANCHORS.items():
        start, end = locate_unique(text, anchor)
        if start <= previous_end:
            raise ValueError("Claim anchors are not in original document order")
        previous_end = end
        original = indexed[claim_id]
        if not original["candidate_only"] or original["candidate_validity"] != "undetermined":
            raise ValueError("Attempt to import already-promoted row")
        resolved.append({
            "candidate_id": original["candidate_id"],
            "source_id": original["source_id"],
            "source_uri": pub["url"],
            "source_sha256": hashlib.sha256(raw).hexdigest(),
            "normalized_text_sha256": hashlib.sha256(
                text.encode("utf-8")).hexdigest(),
            "span_basis": "Unicode characters in whitespace-normalized HTML text",
            "span_start": start,
            "span_end": end,
            "anchor": text[start:end],
            "subject": original["subject"],
            "predicate": original["predicate"],
            "object": original["object"],
            "event_date": original["source_event_time"],
            "publication_date": original["source_publication_time"],
            "semantic_review_receipt": None,
            "candidate_only": True,
            "validity": "undetermined",
            "does_not_claim": [
                "original scan authenticity",
                "reviewed EventPNF admission",
                "implementation of the 1998 draft",
                "causal persuasion or policy effect",
            ],
        })
    return {
        "schema": "dashi.ccdcoe.p3.offline_candidate_spans.v1",
        "source_uri": pub["url"],
        "raw_sha256": hashlib.sha256(raw).hexdigest(),
        "normalized_sha256": hashlib.sha256(text.encode()).hexdigest(),
        "raw_byte_count": len(raw),
        "candidate_count": len(resolved),
        "rows": resolved,
        "review_status": "UNREVIEWED_CANDIDATE_ONLY",
    }

def acquire_govinfo() -> bytes:
    """Acquire only the exact pinned government page, with bounded bytes."""
    req = Request(OFFICIAL_URL, headers={
        "User-Agent": "DASHI-P3-evidence-audit/1.0",
        "Accept": "text/html",
    })
    with urlopen(req, timeout=25) as response:
        if response.geturl() != OFFICIAL_URL:
            raise ValueError("Unexpected redirect away from exact GovInfo URL")
        if response.status != 200:
            raise ValueError(f"Unexpected GovInfo HTTP status {response.status}")
        media_type = response.headers.get_content_type()
        if media_type not in ("text/html", "text/plain"):
            raise ValueError(f"Unexpected GovInfo content type {media_type}")
        declared = response.headers.get("Content-Length")
        if declared is not None and int(declared) > MAX_SOURCE_BYTES:
            raise ValueError("Remote file exceeds size limit")
        raw = response.read(MAX_SOURCE_BYTES + 1)
        if len(raw) > MAX_SOURCE_BYTES:
            raise ValueError("Remote file exceeds size limit")
    return raw


def write_archived_bytes(path: Path, raw: bytes) -> None:
    """Write a byte-for-byte source copy without silently overwriting history."""
    if path.exists():
        existing = path.read_bytes()
        if hashlib.sha256(existing).digest() != hashlib.sha256(raw).digest():
            raise ValueError(f"Archive already exists with different bytes: {path}")
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        mode="wb", dir=path.parent, prefix=path.name + ".",
        suffix=".partial", delete=False
    ) as stream:
        temporary_path = Path(stream.name)
        try:
            stream.write(raw)
        except BaseException:
            temporary_path.unlink(missing_ok=True)
            raise
    try:
        # Hard-link creates without replacing existing path; unlike os.replace
        # it does not overwrite a concurrently-created historical receipt.
        os.link(temporary_path, path)
    except FileExistsError:
        if path.read_bytes() != raw:
            raise ValueError("Concurrent archive has different bytes")
    finally:
        temporary_path.unlink(missing_ok=True)


def self_test() -> None:
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    fake = "<html><body>Global Climate Science\n" + "\n".join(
        ANCHORS.values()) + "</body></html>"
    fixture = fake.encode()
    result = prepare(fixture, manifest)
    assert result["candidate_count"] == 6
    assert all(r["candidate_only"] and r["validity"] == "undetermined"
               and r["semantic_review_receipt"] is None for r in result["rows"])
    assert len({r["source_sha256"] for r in result["rows"]}) == 1
    for row in result["rows"]:
        assert row["span_end"] > row["span_start"]
    try:
        prepare((fake + ANCHORS["document_circulation"]).encode(), manifest)
    except ValueError:
        pass
    else:
        raise AssertionError("Duplicate anchor was not rejected")
    try:
        prepare(b"<html>unrelated subject</html>", manifest)
    except ValueError:
        pass
    else:
        raise AssertionError("Unrelated source was not rejected")
    reordered = "<html>Global Climate Science " + "\n".join(reversed(list(ANCHORS.values()))) + "</html>"
    try:
        prepare(reordered.encode(), manifest)
    except ValueError:
        pass
    else:
        raise AssertionError("Reordered source sections were not rejected")
    print("PASS: six ordered candidate offsets, deterministic hashes, duplicate/reorder/source rejection")

def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    inputs = p.add_mutually_exclusive_group()
    inputs.add_argument("--source", type=Path)
    inputs.add_argument("--fetch-govinfo", action="store_true")
    p.add_argument("--archive", type=Path,
                   help="Required with --fetch-govinfo; immutable original bytes")
    p.add_argument("--output", type=Path)
    p.add_argument("--self-test", action="store_true")
    a = p.parse_args()
    if a.self_test:
        self_test()
        return
    if a.output is None:
        p.error("--output is required")
    if a.fetch_govinfo:
        if a.archive is None:
            p.error("--archive is required with --fetch-govinfo")
        raw = acquire_govinfo()
    elif a.source is not None:
        if a.archive is not None:
            p.error("--archive is only accepted with --fetch-govinfo")
        raw = a.source.read_bytes()
    else:
        p.error("choose --source or --fetch-govinfo")
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    result = prepare(raw, manifest)
    if a.fetch_govinfo:
        write_archived_bytes(a.archive, raw)
        result["local_archive_path"] = str(a.archive)
        result["acquisition_mode"] = "exact-govinfo-url-with-byte-archive"
    else:
        result["acquisition_mode"] = "user-supplied-original-byte-file"
    a.output.parent.mkdir(parents=True, exist_ok=True)
    a.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(f"Source SHA256: {result['raw_sha256']}")
    print(f"Candidate span output written: {a.output} (review remains OPEN)")

if __name__ == "__main__":
    main()
