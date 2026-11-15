#!/usr/bin/env python3
"""Revision-locked ORIGINAL Wikipedia wikitext -> first qualified link receipt.

Uses DASHI's separately attributed behavioural port of Ibrahim et al.'s
historical first_link_txt.py. The actual page revision must be supplied as
full original MediaWiki Action API JSON bytes, with an independent raw SHA.
Does not claim the archived 2016 parser ran, a title equals a Wikidata QID,
or a Zelph Wikidata edge means Wikipedia's first qualified hyperlink.
"""
from __future__ import annotations

import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys
from typing import Any

from ibrahim_author_parser_port import (
    SOURCE_BLOB, reference_first_qualifying_link,
)


def _strict(raw: bytes) -> dict:
    def pairs(kvs):
        output = {}
        for key, value in kvs:
            if key in output:
                raise ValueError("duplicate original MediaWiki JSON key: " + key)
            output[key] = value
        return output
    result = json.loads(raw.decode("utf-8"), object_pairs_hook=pairs,
                        parse_constant=lambda n: (_ for _ in ()).throw(
                            ValueError("non-JSON numeric token: " + n)))
    if type(result) is not dict:
        raise ValueError("full MediaWiki Action API response required")
    return result


def audit_revision(*, raw: bytes, pinned_raw_sha256: str,
                   oldid: int, pageid: int,
                   expected_title: str | None = None,
                   expected_target: str | None = None) -> dict[str, Any]:
    if (type(pinned_raw_sha256) is not str or len(pinned_raw_sha256) != 64
            or any(c not in "0123456789abcdef" for c in pinned_raw_sha256)
            or sha256(raw).hexdigest() != pinned_raw_sha256):
        raise ValueError("original raw MediaWiki API bytes require matching independently supplied digest")
    if (type(oldid) is not int or oldid <= 0 or
            type(pageid) is not int or pageid <= 0):
        raise ValueError("positive exact original pageid and oldid required")
    response = _strict(raw)
    if response.get("batchcomplete") is False:
        raise ValueError("truncated original page result")
    pages = (response.get("query") or {}).get("pages")
    if type(pages) is not list or len(pages) != 1:
        raise ValueError("expected one exact original page in formatversion=2 response")
    page = pages[0]
    if (type(page) is not dict or type(page.get("pageid")) is not int
            or page["pageid"] != pageid):
        raise ValueError("pageid mismatch")
    title = page.get("title")
    if not isinstance(title, str) or not title:
        raise ValueError("missing original page title")
    if expected_title is not None and title != expected_title:
        raise ValueError("original title differs from externally pinned value")
    revisions = page.get("revisions")
    if type(revisions) is not list or len(revisions) != 1:
        raise ValueError("expected one original revision only")
    rev = revisions[0]
    if type(rev) is not dict or type(rev.get("revid")) is not int or rev["revid"] != oldid:
        raise ValueError("oldid/revid mismatch")
    slots = rev.get("slots")
    if type(slots) is not dict or type(slots.get("main")) is not dict:
        raise ValueError("full main wikitext revision slot required")
    main = slots["main"]
    if main.get("contentmodel") not in (None, "wikitext"):
        raise ValueError("non-wikitext page revision")
    text = main.get("content", main.get("*"))
    if not isinstance(text, str):
        raise ValueError("missing exact main wikitext slot bytes")
    if len(text.encode("utf-8")) > 32 * 1024 * 1024:
        raise ValueError("per-page wikitext exceeds explicit budget")
    first = reference_first_qualifying_link(text)
    if expected_target is not None and (first is None or
                                         first["selected_target"] != expected_target):
        raise ValueError("first qualifying hyperlink differs from independent expectation")
    return {
        "version": "dashi.wikipedia.original_revision_first_qualified_link.v1",
        "pageid": pageid, "oldid": oldid, "title": title,
        "main_slot_contentmodel": main.get("contentmodel", "wikitext"),
        "revision_timestamp": rev.get("timestamp"),
        "raw_original_api_sha256_matched_supplied_pin": pinned_raw_sha256,
        "exact_wikitext_utf8_sha256": sha256(text.encode("utf-8")).hexdigest(),
        "first_qualified_link": first,
        "reference_parser_source_blob": SOURCE_BLOB,
        "historical_original_author_code_executed": False,
        "original_dump_producer_corpus_reproduced": False,
        "wikidata_qid_same_object_authenticated": False,
        "zelph_edge_equals_wikipedia_first_link_proved": False,
        "source_support_paid": False,
        "edit_authority": False,
    }


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--raw-api", type=Path, required=True)
    p.add_argument("--expected-raw-sha256", required=True)
    p.add_argument("--oldid", type=int, required=True)
    p.add_argument("--pageid", type=int, required=True)
    p.add_argument("--expected-title")
    p.add_argument("--expected-target")
    p.add_argument("--output", type=Path)
    args = p.parse_args()
    try:
        if not 0 < args.raw_api.stat().st_size <= 64 * 1024 * 1024:
            raise ValueError("bounded original MediaWiki API response required")
        result = audit_revision(
            raw=args.raw_api.read_bytes(), pinned_raw_sha256=args.expected_raw_sha256,
            oldid=args.oldid, pageid=args.pageid, expected_title=args.expected_title,
            expected_target=args.expected_target)
        body = json.dumps(result, sort_keys=True, ensure_ascii=False, indent=2) + "\n"
        if args.output:
            with args.output.open("x", encoding="utf-8") as f:
                f.write(body)
        else:
            print(body, end="")
        return 0
    except (OSError, ValueError, KeyError, TypeError, UnicodeDecodeError) as exc:
        print(json.dumps({"status": "blocked", "reason": str(exc),
                          "edit_authority": False}), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
