#!/usr/bin/env python3
"""Reproducible, fail-closed OFFLINE source-byte to candidate-PNF span bridge.

Usage:
  python3 scripts/build_ccdcoe_p3_primary_intake.py --self-test
  python3 scripts/build_ccdcoe_p3_primary_intake.py \
      --source /path/to/govinfo-1998-record.html \
      --output /path/to/ccdcoe-p3-candidates.json

The source must be obtained independently and provenance-reviewed. No HTTP
fetching, no implicit Wikidata/entity equivalence, no automatic admission.
SHA256 covers the raw input BYTES. All character offsets refer explicitly
to normalized extracted text, not raw HTML bytes or Agda SpanReceipt tokens.
"""
from __future__ import annotations
import argparse
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "Docs/research/ccdcoe_p3_climate_case_manifest.json"
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
    if not pub["url"].startswith("https://www.govinfo.gov/"):
        raise ValueError("Unexpected canonical source locator")
    rows = manifest["pnf_candidate_intake"]
    indexed = {row["candidate_id"].removeprefix("pnf-"): row for row in rows}
    if set(indexed) != set(ANCHORS):
        raise ValueError("Manifest candidate identities do not match anchors")
    resolved = []
    for claim_id, anchor in ANCHORS.items():
        start, end = locate_unique(text, anchor)
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
    print("PASS: six distinct candidate offsets, deterministic hashes, duplicate/source rejection")

def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--source", type=Path)
    p.add_argument("--output", type=Path)
    p.add_argument("--self-test", action="store_true")
    a = p.parse_args()
    if a.self_test:
        self_test()
        return
    if a.source is None or a.output is None:
        p.error("--source and --output required unless --self-test")
    raw = a.source.read_bytes()
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    result = prepare(raw, manifest)
    a.output.parent.mkdir(parents=True, exist_ok=True)
    a.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(f"Candidate span output written: {a.output} (review remains OPEN)")

if __name__ == "__main__":
    main()
