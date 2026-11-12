#!/usr/bin/env python3
"""Index only explicitly printed Rhea identifiers from supplied source text.

Read from an authorized local copy of Kitzerow's chart text. Do not download
or redistribute original CC BY-NC-ND 4.0 diagrams. Preserve byte digest and
line/column coordinates, including the ResearchGate private-use font glyphs
observed in its HTML text extraction.

Kitzerow: BH4/Folate/Cobalamin/Homocysteine Pathway, ResearchGate 377218425
(declared 2024-01; available webpage shows later 2025-08-08 full-text upload).
Rhea owns underlying reaction identities; DASHI owns this candidate extractor.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import unicodedata
from pathlib import Path

# Public ResearchGate text extraction of the chart includes "R",
# with glyphs U+F768, U+F765 and U+F761 (font-private h/e/a).
# This is an exact observed encoding shim, not general OCR or transliteration.
_PRIVATE_RHEA_GLYPHS = {ord("\uf768"): "h", ord("\uf765"): "e", ord("\uf761"): "a"}
_RHEA = re.compile(r"(?<![A-Za-z0-9])Rhea\s*[:#]?\s*([0-9]{4,6})\b", re.IGNORECASE)

SCHEMA = "dashi.kitzerow-chart-source-text-identifier-candidates.v1"


def index_text(raw: bytes, *, source_url: str, source_revision: str) -> dict:
    if not raw or not source_url.startswith("https://www.researchgate.net/publication/377218425_"):
        raise ValueError("missing source bytes or unexpected source URL")
    if not source_revision:
        raise ValueError("source revision/upload observation required")
    content = raw.decode("utf-8", errors="strict")
    out = []
    for row_no, original in enumerate(content.splitlines(), 1):
        normalized = unicodedata.normalize("NFKC", original.translate(_PRIVATE_RHEA_GLYPHS))
        for matched in _RHEA.finditer(normalized):
            # Column refers to *normalized* web text; before Unicode expansion
            # original column equivalence is not independently established.
            out.append({
                "rhea_id": "RHEA:" + matched.group(1),
                "source_text_line": row_no,
                "normalized_line_column": matched.start() + 1,
                "source_anchor_kind": "local-text-line-not-pdf-page",
                "review_status": "candidate-unverified-figure-location",
            })
    ids = sorted({row["rhea_id"] for row in out})
    return {
        "schema": SCHEMA,
        "creator": "Kimberly Kitzerow",
        "source_url": source_url,
        "source_revision": source_revision,
        "source_utf8_sha256": hashlib.sha256(raw).hexdigest(),
        "source_is_faithful_publisher_binary": False,
        "creator_pdf_figure_geometry_verified": False,
        "text_observed_reaction_ids": ids,
        "occurrences": sorted(out, key=lambda r: (r["source_text_line"],
                                                  r["normalized_line_column"], r["rhea_id"])),
        "source_text_observation_complete_only_for_supplied_bytes": True,
        "not_creator_full_network_coverage": True,
        "candidate_only": True,
        "establishes_physical_flux": False,
        "establishes_causal_model": False,
    }


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--source-text", type=Path, required=True,
                   help="authorized source text extraction; do not commit copyrighted full chart")
    p.add_argument("--source-url", default=(
        "https://www.researchgate.net/publication/377218425_BH4FolateCobalaminHomocysteine_Pathway"))
    p.add_argument("--source-revision", required=True,
                   help="caller-observed revision/date; not independent authentication")
    p.add_argument("-o", "--output", type=Path, required=True)
    a = p.parse_args()
    packet = index_text(a.source_text.read_bytes(),
                        source_url=a.source_url,
                        source_revision=a.source_revision)
    a.output.parent.mkdir(parents=True, exist_ok=True)
    a.output.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"unique_rhea_ids": len(packet["text_observed_reaction_ids"]),
                      "occurrences": len(packet["occurrences"]),
                      "digest": packet["source_utf8_sha256"],
                      "review": "candidate-only"}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
