#!/usr/bin/env python3
"""Deterministic positive/negative tests over tiny original-like sample strings."""
from __future__ import annotations

from index_kitzerow_chart_source_text import index_text

URL = "https://www.researchgate.net/publication/377218425_BH4FolateCobalaminHomocysteine_Pathway"


def rejects(raw: bytes, url: str = URL, revision: str = "2025-08-08") -> None:
    try:
        index_text(raw, source_url=url, source_revision=revision)
    except (ValueError, UnicodeDecodeError):
        return
    raise AssertionError("bad chart text admitted")


def main() -> int:
    text = "R 21708\nRhea:21080\nRHEA 21708\nirrelevant 99999\n"
    x = index_text(text.encode("utf8"), source_url=URL, source_revision="2025-08-08")
    assert x["text_observed_reaction_ids"] == ["RHEA:21080", "RHEA:21708"]
    assert len(x["occurrences"]) == 3
    assert x["occurrences"][0]["source_text_line"] == 1
    assert x["source_is_faithful_publisher_binary"] is False
    assert x["not_creator_full_network_coverage"] is True
    assert x == index_text(text.encode("utf8"), source_url=URL, source_revision="2025-08-08")
    rejects(b"")
    rejects(b"\xff\xfe")
    rejects(b"Rhea 21708", url="https://example.org/unrelated")
    rejects(b"Rhea 21708", revision="")
    print("Kitzerow chart source-text ID extraction regression: ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
