#!/usr/bin/env python3
"""Acquire bounded Wikidata/Wikipedia identity receipts for the BH4 protein panel.

The resolver treats Wikimedia as an external identity/provenance surface, not a
biological authority. Protein identity is accepted only when a Wikidata item
carries an exact P352 (UniProt protein ID) match for the requested accession.
The primary resolver is an exact WDQS P352 query; MediaWiki text search is kept
only as diagnostic provenance and never establishes identity.

Gene/protein identity stays separate: P702 (encoded by) and reciprocal P688
(encodes) are recorded independently. English-Wikipedia page/revision
coordinates are pinned when a sitelink exists.

Examples:

    python3 scripts/acquire_wikimedia_bio_identity.py P09417
    python3 scripts/acquire_wikimedia_bio_identity.py --kitzerow-bh4-panel -o panel.json

The panel list is imported from acquire_uniprot_bio_certificate.py so the two
acquisition lanes cannot silently drift to different accessions.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
import urllib.error
import urllib.parse
import urllib.request
import time
from datetime import datetime, timezone
from pathlib import Path

from acquire_uniprot_bio_certificate import KITZEROW_BH4_PANEL

WIKIDATA_API = "https://www.wikidata.org/w/api.php"
WIKIDATA_SPARQL = "https://query.wikidata.org/sparql"
ENWIKI_API = "https://en.wikipedia.org/w/api.php"
HUMAN_QID = "Q5"


def _get_json(base: str, params: dict[str, str], max_retries: int = 5) -> tuple[dict, bytes]:
    query = urllib.parse.urlencode(params)
    request = urllib.request.Request(
        f"{base}?{query}",
        headers={
            "Accept": "application/sparql-results+json, application/json",
            "User-Agent": "DASHI-wikimedia-biology-acquisition/1.1 (https://github.com/chboishabba/dashi_agda; contact: johlbrown@gmail.com)",
        },
    )
    for attempt in range(max_retries):
        try:
            with urllib.request.urlopen(request, timeout=15) as response:
                raw = response.read()
            return json.loads(raw), raw
        except urllib.error.HTTPError as exc:
            if exc.code == 429 and attempt < max_retries - 1:
                wait_time = 2.0 * (attempt + 1)
                time.sleep(wait_time)
                continue
            raise


def _claim_entity_ids(entity: dict, prop: str) -> list[str]:
    result: list[str] = []
    for claim in entity.get("claims", {}).get(prop, []):
        value = claim.get("mainsnak", {}).get("datavalue", {}).get("value")
        if isinstance(value, dict) and isinstance(value.get("id"), str):
            result.append(value["id"])
    return result


def _claim_strings(entity: dict, prop: str) -> list[str]:
    result: list[str] = []
    for claim in entity.get("claims", {}).get(prop, []):
        value = claim.get("mainsnak", {}).get("datavalue", {}).get("value")
        if isinstance(value, str):
            result.append(value)
    return result


def search_candidates(accession: str) -> list[str]:
    payload, _ = _get_json(
        WIKIDATA_API,
        {
            "action": "wbsearchentities",
            "search": accession,
            "language": "en",
            "type": "item",
            "limit": "50",
            "format": "json",
        },
    )
    return [row["id"] for row in payload.get("search", []) if row.get("id")]


def exact_p352_qids(accession: str) -> tuple[list[str], str]:
    if not accession.isalnum():
        raise ValueError(f"invalid UniProt accession for exact P352 query: {accession!r}")
    sparql = f'SELECT DISTINCT ?item WHERE {{ ?item wdt:P352 "{accession}". }}'
    payload, raw = _get_json(
        WIKIDATA_SPARQL,
        {"query": sparql, "format": "json"},
    )
    qids: list[str] = []
    for row in payload.get("results", {}).get("bindings", []):
        value = row.get("item", {}).get("value", "")
        if value.startswith("http://www.wikidata.org/entity/Q"):
            qids.append(value.rsplit("/", 1)[-1])
    return sorted(set(qids)), hashlib.sha256(raw).hexdigest()


def fetch_entities(qids: list[str]) -> tuple[dict[str, dict], str]:
    if not qids:
        return {}, ""
    payload, raw = _get_json(
        WIKIDATA_API,
        {
            "action": "wbgetentities",
            "ids": "|".join(qids),
            "props": "labels|descriptions|claims|sitelinks|info",
            "languages": "en",
            "sitefilter": "enwiki",
            "format": "json",
        },
    )
    return payload.get("entities", {}), hashlib.sha256(raw).hexdigest()


def exact_protein_candidates(accession: str) -> tuple[list[dict], list[str], str, list[str]]:
    exact_qids, sparql_sha = exact_p352_qids(accession)
    searched = search_candidates(accession)
    entities, _ = fetch_entities(exact_qids)
    exact: list[dict] = []
    for qid in exact_qids:
        entity = entities.get(qid, {})
        if accession in _claim_strings(entity, "P352"):
            exact.append(entity)
    return exact, exact_qids, sparql_sha, searched


def fetch_gene_receipt(gene_qid: str, protein_qid: str) -> dict:
    entities, raw_sha = fetch_entities([gene_qid])
    gene = entities.get(gene_qid, {})
    encodes = _claim_entity_ids(gene, "P688")
    return {
        "gene_qid": gene_qid,
        "gene_label": gene.get("labels", {}).get("en", {}).get("value"),
        "gene_wikidata_lastrevid": gene.get("lastrevid"),
        "gene_entity_response_sha256": raw_sha,
        "p688_encodes_targets": encodes,
        "reciprocal_p688_paid": protein_qid in encodes,
    }


def fetch_enwiki(title: str | None) -> dict:
    if not title:
        return {
            "present": False,
            "title": None,
            "pageid": None,
            "lastrevid": None,
            "wikibase_item": None,
            "qid_round_trip_paid": False,
            "response_sha256": None,
        }
    payload, raw = _get_json(
        ENWIKI_API,
        {
            "action": "query",
            "titles": title,
            "prop": "info|pageprops",
            "redirects": "1",
            "format": "json",
        },
    )
    pages = payload.get("query", {}).get("pages", {})
    page = next(iter(pages.values()), {})
    present = "missing" not in page and int(page.get("pageid", -1)) >= 0
    wikibase_item = page.get("pageprops", {}).get("wikibase_item") if present else None
    return {
        "present": present,
        "title": page.get("title", title),
        "pageid": page.get("pageid") if present else None,
        "lastrevid": page.get("lastrevid") if present else None,
        "wikibase_item": wikibase_item,
        "qid_round_trip_paid": False,
        "response_sha256": hashlib.sha256(raw).hexdigest(),
    }


def build_identity(accession: str, symbol: str | None = None, sector: str | None = None) -> dict:
    exact, exact_qids, sparql_sha, searched = exact_protein_candidates(accession)
    rows: list[dict] = []
    for protein in exact:
        qid = protein.get("id")
        encoded_by = _claim_entity_ids(protein, "P702")
        taxa = _claim_entity_ids(protein, "P703")
        sitelink = protein.get("sitelinks", {}).get("enwiki", {})
        enwiki_title = sitelink.get("title")
        gene_receipts = [fetch_gene_receipt(gene_qid, qid) for gene_qid in encoded_by]
        enwiki = fetch_enwiki(enwiki_title)
        if enwiki["present"]:
            enwiki["qid_round_trip_paid"] = enwiki.get("wikibase_item") == qid
        _, raw_sha = fetch_entities([qid])
        rows.append(
            {
                "protein_qid": qid,
                "protein_label": protein.get("labels", {}).get("en", {}).get("value"),
                "protein_description": protein.get("descriptions", {}).get("en", {}).get("value"),
                "wikidata_lastrevid": protein.get("lastrevid"),
                "wikidata_entity_response_sha256": raw_sha,
                "p352_uniprot_ids": _claim_strings(protein, "P352"),
                "exact_p352_match": accession in _claim_strings(protein, "P352"),
                "p702_encoded_by": encoded_by,
                "p703_taxa": taxa,
                "human_taxon_paid": HUMAN_QID in taxa,
                "gene_receipts": gene_receipts,
                "enwiki": enwiki,
            }
        )

    unique_exact = len(rows) == 1
    return {
        "identity_schema": "dashi.wikimedia-biology-identity.v1",
        "acquired_at_utc": datetime.now(timezone.utc).isoformat(),
        "symbol": symbol,
        "sector": sector,
        "uniprot_accession": accession,
        "resolver": "exact WDQS wdt:P352 followed by wbgetentities claim verification",
        "exact_p352_qids": exact_qids,
        "exact_p352_query_response_sha256": sparql_sha,
        "diagnostic_text_search_qids": searched,
        "exact_p352_matches": rows,
        "exact_match_count": len(rows),
        "unique_exact_protein_qid": unique_exact,
        "identity_status": "verified" if unique_exact else ("ambiguous" if rows else "unresolved"),
        "promotion_boundary": {
            "qid_creates_sequence_identity": False,
            "qid_creates_biological_truth": False,
            "wikidata_statement_creates_mechanistic_evidence": False,
            "wikipedia_narrative_creates_mechanistic_evidence": False,
            "gene_qid_equals_protein_qid": False,
            "wikimedia_identity_confirms_whole_kitzerow_graph": False,
        },
    }


def acquire_panel() -> tuple[dict, int]:
    members: list[dict] = []
    for member in KITZEROW_BH4_PANEL:
        print(f"Acquiring {member['symbol']} ({member['accession']})...", file=sys.stderr, flush=True)
        try:
            members.append(build_identity(member["accession"], member["symbol"], member["sector"]))
        except (urllib.error.URLError, urllib.error.HTTPError, TimeoutError, json.JSONDecodeError, ValueError) as exc:
            members.append(
                {
                    "symbol": member["symbol"],
                    "sector": member["sector"],
                    "uniprot_accession": member["accession"],
                    "identity_status": "acquisition-error",
                    "error": str(exc),
                }
            )
        time.sleep(0.5)

    verified = sum(row.get("identity_status") == "verified" for row in members)
    ambiguous = sum(row.get("identity_status") == "ambiguous" for row in members)
    unresolved = sum(row.get("identity_status") == "unresolved" for row in members)
    errors = sum(row.get("identity_status") == "acquisition-error" for row in members)
    result = {
        "panel_schema": "dashi.wikimedia-biology-panel.v1",
        "panel_id": "kitzerow-bh4-wikimedia-identity",
        "requested_members": len(KITZEROW_BH4_PANEL),
        "verified_unique_members": verified,
        "ambiguous_members": ambiguous,
        "unresolved_members": unresolved,
        "acquisition_errors": errors,
        "complete_unique_identity": verified == len(KITZEROW_BH4_PANEL),
        "members": members,
        "promotion_boundary": {
            "complete_identity_panel_creates_biological_truth": False,
            "complete_identity_panel_creates_allocator_flux": False,
            "wikipedia_coverage_creates_mechanistic_support": False,
        },
    }
    return result, 0 if errors == 0 else 3


def render(payload: dict, output: Path | None) -> None:
    text = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if output:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("accession", nargs="?", help="UniProt accession")
    parser.add_argument("--symbol")
    parser.add_argument("--kitzerow-bh4-panel", action="store_true")
    parser.add_argument("-o", "--output", type=Path)
    args = parser.parse_args()

    if args.kitzerow_bh4_panel and args.accession:
        parser.error("choose either one accession or --kitzerow-bh4-panel")
    if not args.kitzerow_bh4_panel and not args.accession:
        parser.error("provide an accession or --kitzerow-bh4-panel")

    if args.kitzerow_bh4_panel:
        payload, exit_code = acquire_panel()
        render(payload, args.output)
        return exit_code

    try:
        payload = build_identity(args.accession.strip().upper(), args.symbol)
    except (urllib.error.URLError, urllib.error.HTTPError, TimeoutError, json.JSONDecodeError, ValueError) as exc:
        print(f"Wikimedia identity acquisition failed: {exc}", file=sys.stderr)
        return 2
    render(payload, args.output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
