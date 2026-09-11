#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any
from urllib.parse import unquote, urlparse

SCHEMA = "slr-gwb-wikimedia-seed-candidates-v2"
PROJECTION_SCHEMA = "sensiblaw.gwb-source-projection.v0_1"
OVERLAY_SCHEMA = "slr-gwb-reviewed-wikimedia-identities-v1"
QID_RE = re.compile(r"^Q[1-9][0-9]*$")


def load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise SystemExit(f"expected JSON object: {path}")
    return value


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    if not path.exists():
        return rows
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        value = json.loads(line)
        if not isinstance(value, dict):
            raise SystemExit(f"expected JSON object row: {path}")
        rows.append(value)
    return rows


def first_string(obj: dict[str, Any], names: tuple[str, ...]) -> str:
    for name in names:
        value = obj.get(name)
        if isinstance(value, str) and value.strip():
            return value.strip()
    return ""


def qid_from_url(value: str) -> str:
    if not value:
        return ""
    parsed = urlparse(value)
    if parsed.netloc.lower() not in {"www.wikidata.org", "wikidata.org"}:
        return ""
    tail = parsed.path.rstrip("/").split("/")[-1]
    return tail if QID_RE.fullmatch(tail) else ""


def wikipedia_title_from_url(value: str) -> str:
    if not value:
        return ""
    parsed = urlparse(value)
    host = parsed.netloc.lower()
    if not host.endswith(".wikipedia.org"):
        return ""
    marker = "/wiki/"
    if marker not in parsed.path:
        return ""
    return unquote(parsed.path.split(marker, 1)[1]).replace("_", " ").strip()


def candidate_for_document(doc: dict[str, Any], overlay: dict[str, Any] | None) -> dict[str, Any] | None:
    ordinal = int(doc.get("document_ordinal", -1))
    overlay = overlay or {}

    explicit_qid = first_string(overlay, ("qid", "wikidata_qid", "subject_qid", "primary_qid"))
    if not explicit_qid:
        explicit_qid = first_string(doc, ("wikidata_qid", "subject_qid", "qid", "primary_qid"))
    if explicit_qid and not QID_RE.fullmatch(explicit_qid):
        explicit_qid = ""

    explicit_wikipedia = first_string(
        overlay,
        ("wikipedia_title", "subject_wikipedia_title", "wikipedia_page", "subject_wikipedia_page"),
    )
    if not explicit_wikipedia:
        explicit_wikipedia = first_string(
            doc,
            ("wikipedia_title", "subject_wikipedia_title", "wikipedia_page", "subject_wikipedia_page"),
        )

    source_url = first_string(doc, ("source_url", "url", "canonical_url", "source_reference"))
    if not explicit_qid:
        explicit_qid = qid_from_url(source_url)
    if not explicit_wikipedia:
        explicit_wikipedia = wikipedia_title_from_url(source_url)

    search_label = first_string(
        overlay,
        ("search_label", "subject_label", "subject", "source_title", "document_title", "title", "source_name", "label"),
    )
    if not search_label:
        search_label = first_string(
            doc,
            ("subject_label", "subject", "source_title", "document_title", "title", "source_name", "label"),
        )

    reviewed_overlay = bool(overlay)
    if explicit_qid:
        state = "reviewed-explicit-qid" if reviewed_overlay else "explicit-qid"
    elif explicit_wikipedia:
        state = "reviewed-explicit-wikipedia-title" if reviewed_overlay else "explicit-wikipedia-title"
    elif search_label:
        state = "reviewed-metadata-search-candidate" if reviewed_overlay else "metadata-search-candidate"
    else:
        return None

    return {
        "schema": SCHEMA,
        "seed_id": f"gwb-document:{ordinal}:wikimedia-seed",
        "document_ordinal": ordinal,
        "qid": explicit_qid,
        "wikipedia_title": explicit_wikipedia,
        "search_label": search_label,
        "seed_state": state,
        "coordinate_role": str(overlay.get("coordinate_role", "")),
        "identity_scope": str(overlay.get("identity_scope", "")),
        "review_status": str(overlay.get("review_status", "")),
        "review_reference": str(overlay.get("review_reference", "")),
        "reviewed_overlay_applied": reviewed_overlay,
        "source_sha256": str(doc.get("source_sha256", "")),
        "projected_sha256": str(doc.get("projected_sha256", "")),
        "family_refs": [str(v) for v in (doc.get("family_refs") or [])],
        "topic_anchor_is_source_object_identity": False,
        "metadata_search_is_identity": False,
        "candidate_only": True,
        "semantic_promotion": False,
    }


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--projection-manifest", type=Path, required=True)
    p.add_argument("--reviewed-overlay", type=Path)
    p.add_argument("--output", type=Path, required=True)
    return p.parse_args()


def main() -> int:
    args = parse_args()
    manifest = load(args.projection_manifest)
    if manifest.get("schema_version") != PROJECTION_SCHEMA:
        raise SystemExit(f"unexpected projection schema: {manifest.get('schema_version')!r}")

    overlay_by_ordinal: dict[int, dict[str, Any]] = {}
    if args.reviewed_overlay is not None:
        for row in read_jsonl(args.reviewed_overlay):
            if row.get("schema") != OVERLAY_SCHEMA:
                raise SystemExit(f"unexpected reviewed overlay schema: {row.get('schema')!r}")
            ordinal = int(row.get("document_ordinal", -1))
            if ordinal in overlay_by_ordinal:
                raise SystemExit(f"duplicate reviewed overlay document ordinal: {ordinal}")
            if bool(row.get("semantic_promotion", False)):
                raise SystemExit("reviewed identity overlay must not claim semantic promotion")
            overlay_by_ordinal[ordinal] = row

    documents = [d for d in (manifest.get("documents") or []) if isinstance(d, dict)]
    seeds = [
        s
        for d in documents
        if (s := candidate_for_document(d, overlay_by_ordinal.get(int(d.get("document_ordinal", -1))))) is not None
    ]
    seeded_ordinals = {int(s["document_ordinal"]) for s in seeds}
    missing = sorted(
        int(d.get("document_ordinal", -1))
        for d in documents
        if int(d.get("document_ordinal", -1)) not in seeded_ordinals
    )

    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", encoding="utf-8") as handle:
        for seed in seeds:
            handle.write(json.dumps(seed, sort_keys=True) + "\n")

    explicit_qid = sum(s["seed_state"].endswith("explicit-qid") for s in seeds)
    explicit_wikipedia = sum(s["seed_state"].endswith("explicit-wikipedia-title") for s in seeds)
    metadata_search = sum(s["seed_state"].endswith("metadata-search-candidate") for s in seeds)
    reviewed = sum(bool(s["reviewed_overlay_applied"]) for s in seeds)
    print(
        "SLR_GWB_WIKIMEDIA_SEED_RECEIPT "
        f"schema={SCHEMA} documents={len(documents)} seeds={len(seeds)} reviewed={reviewed} "
        f"explicit_qid={explicit_qid} explicit_wikipedia={explicit_wikipedia} "
        f"metadata_search_candidates={metadata_search} unseeded={len(missing)} "
        "topic_anchor_is_source_object_identity=false metadata_search_is_identity=false "
        "candidate_only=true semantic_promotion=false",
        file=sys.stderr,
    )
    if missing:
        print(
            "SLR_GWB_WIKIMEDIA_SEED_RESIDUAL unseeded_document_ordinals="
            + ",".join(map(str, missing)),
            file=sys.stderr,
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
