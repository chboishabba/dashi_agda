#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
import urllib.parse
import urllib.request
from collections import deque
from copy import deepcopy
from pathlib import Path
from typing import Any

SCHEMA = "slr-wikimedia-world-follow-v1"
TARGET_SCHEMA = "sl.candidate_world_model.v0_1"
WIKIDATA_API = "https://www.wikidata.org/w/api.php"
WIKIPEDIA_API = "https://en.wikipedia.org/w/api.php"

PARENT_PROPERTIES = {"P31", "P279", "P361", "P131"}
CONTEXT_PROPERTIES = {"P17", "P276", "P527", "P155", "P156", "P460", "P1269"}


def load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise SystemExit(f"expected JSON object: {path}")
    return value


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        value = json.loads(line)
        if isinstance(value, dict):
            out.append(value)
    return out


def api_get(base: str, params: dict[str, Any], timeout: float) -> dict[str, Any]:
    p = {k: str(v) for k, v in params.items() if v is not None}
    p.setdefault("format", "json")
    p.setdefault("formatversion", "2")
    url = base + "?" + urllib.parse.urlencode(p)
    req = urllib.request.Request(url, headers={"User-Agent": "DASHI-SLR-WikimediaWorldFollow/1.0"})
    with urllib.request.urlopen(req, timeout=timeout) as response:
        return json.loads(response.read().decode("utf-8"))


def search_qids(label: str, limit: int, timeout: float) -> list[dict[str, Any]]:
    data = api_get(
        WIKIDATA_API,
        {"action": "wbsearchentities", "search": label, "language": "en", "uselang": "en", "type": "item", "limit": limit},
        timeout,
    )
    return [x for x in (data.get("search") or []) if isinstance(x, dict)]


def qid_for_title(title: str, timeout: float) -> tuple[str, str]:
    data = api_get(
        WIKIPEDIA_API,
        {"action": "query", "titles": title, "redirects": 1, "prop": "pageprops"},
        timeout,
    )
    pages = ((data.get("query") or {}).get("pages") or [])
    if not pages:
        return "", title
    page = pages[0]
    return str((page.get("pageprops") or {}).get("wikibase_item", "")), str(page.get("title", title))


def entity(qid: str, timeout: float) -> dict[str, Any]:
    data = api_get(
        WIKIDATA_API,
        {"action": "wbgetentities", "ids": qid, "languages": "en", "props": "labels|descriptions|claims|sitelinks"},
        timeout,
    )
    return ((data.get("entities") or {}).get(qid) or {})


def item_targets(claims: dict[str, Any], max_edges: int) -> list[tuple[str, str]]:
    out: list[tuple[str, str]] = []
    for pid in sorted(claims):
        for statement in claims.get(pid) or []:
            if not isinstance(statement, dict):
                continue
            snak = statement.get("mainsnak") or {}
            value = ((snak.get("datavalue") or {}).get("value"))
            if not isinstance(value, dict):
                continue
            target = value.get("id")
            if isinstance(target, str) and target.startswith("Q"):
                out.append((pid, target))
                if len(out) >= max_edges:
                    return out
    return out


def wikipedia_surface(title: str, max_links: int, timeout: float) -> dict[str, Any]:
    if not title:
        return {"title": "", "categories": [], "links": [], "first_mainspace_link_candidate": ""}
    data = api_get(
        WIKIPEDIA_API,
        {"action": "parse", "page": title, "prop": "links|categories"},
        timeout,
    )
    parse = data.get("parse") or {}
    links = []
    for row in parse.get("links") or []:
        if not isinstance(row, dict) or int(row.get("ns", -1)) != 0:
            continue
        text = str(row.get("title", "")).strip()
        if text and text not in links:
            links.append(text)
        if len(links) >= max_links:
            break
    categories = []
    for row in parse.get("categories") or []:
        if isinstance(row, dict):
            text = str(row.get("category", "")).strip()
            if text and text not in categories:
                categories.append(text)
    return {
        "title": str(parse.get("title", title)),
        "categories": categories,
        "links": links,
        "first_mainspace_link_candidate": links[0] if links else "",
    }


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--world-model", type=Path, required=True)
    p.add_argument("--seeds", type=Path, required=True)
    p.add_argument("--output-model", type=Path, required=True)
    p.add_argument("--output-graph", type=Path, required=True)
    p.add_argument("--max-depth", type=int, default=2)
    p.add_argument("--max-seed-search-results", type=int, default=3)
    p.add_argument("--max-item-properties", type=int, default=80)
    p.add_argument("--max-wikipedia-links", type=int, default=30)
    p.add_argument("--timeout", type=float, default=20.0)
    return p.parse_args()


def main() -> int:
    args = parse_args()
    world = load(args.world_model)
    if world.get("schema_version") != TARGET_SCHEMA:
        raise SystemExit(f"unexpected CandidateWorldModel schema: {world.get('schema_version')!r}")
    if world.get("model_status") != "candidate":
        raise SystemExit("Wikimedia world follow only accepts candidate models")
    if bool((world.get("metadata") or {}).get("semantic_promotion", False)):
        raise SystemExit("refusing semantically promoted input")

    seeds = read_jsonl(args.seeds)
    queue: deque[tuple[str, int, str, str]] = deque()
    seed_receipts: list[dict[str, Any]] = []
    unresolved_seed_count = 0

    for seed in seeds:
        qid = str(seed.get("qid", "")).strip()
        title = str(seed.get("wikipedia_title", "")).strip()
        label = str(seed.get("search_label", "")).strip()
        state = str(seed.get("seed_state", ""))
        candidates: list[dict[str, Any]] = []
        if qid:
            candidates = [{"id": qid, "match_basis": "explicit-qid", "identity_paid": True}]
        elif title:
            resolved_qid, canonical_title = qid_for_title(title, args.timeout)
            if resolved_qid:
                candidates = [{"id": resolved_qid, "match_basis": "explicit-wikipedia-title", "wikipedia_title": canonical_title, "identity_paid": True}]
        elif label:
            for rank, row in enumerate(search_qids(label, args.max_seed_search_results, args.timeout), start=1):
                if row.get("id"):
                    candidates.append({
                        "id": str(row["id"]),
                        "label": row.get("label", ""),
                        "description": row.get("description", ""),
                        "search_rank": rank,
                        "match_basis": "metadata-search-candidate",
                        "identity_paid": False,
                    })
        if not candidates:
            unresolved_seed_count += 1
        for candidate in candidates:
            queue.append((str(candidate["id"]), 0, str(seed.get("seed_id", "")), str(candidate.get("match_basis", state))))
        seed_receipts.append({
            "seed_id": seed.get("seed_id", ""),
            "seed_state": state,
            "candidate_qids": candidates,
            "metadata_search_is_identity": False,
        })

    visited: set[str] = set()
    nodes: dict[str, dict[str, Any]] = {}
    edges: list[dict[str, Any]] = []
    wikipedia_pages: dict[str, dict[str, Any]] = {}
    first_link_candidates: list[dict[str, Any]] = []
    parent_edge_count = 0
    surrounding_edge_count = 0
    first_link_follow_count = 0

    while queue:
        qid, depth, seed_id, route_basis = queue.popleft()
        if qid in visited or depth > args.max_depth:
            continue
        visited.add(qid)
        wd = entity(qid, args.timeout)
        label = str(((wd.get("labels") or {}).get("en") or {}).get("value", qid))
        description = str(((wd.get("descriptions") or {}).get("en") or {}).get("value", ""))
        enwiki = str(((wd.get("sitelinks") or {}).get("enwiki") or {}).get("title", ""))
        nodes[qid] = {
            "node_id": qid,
            "label": label,
            "description": description,
            "wikipedia_title": enwiki,
            "depth": depth,
            "seed_id": seed_id,
            "route_basis": route_basis,
            "identity_coordinate_only": True,
        }

        claims = wd.get("claims") or {}
        targets = item_targets(claims if isinstance(claims, dict) else {}, args.max_item_properties)
        for pid, target in targets:
            relation_class = "parent" if pid in PARENT_PROPERTIES else ("surrounding" if pid in CONTEXT_PROPERTIES else "related-property")
            edges.append({
                "source": qid,
                "target": target,
                "property_id": pid,
                "edge_class": relation_class,
                "native_statement_context_retained": False,
                "semantic_promotion": False,
            })
            if relation_class == "parent":
                parent_edge_count += 1
                if depth < args.max_depth:
                    queue.append((target, depth + 1, seed_id, f"wikidata-parent:{pid}"))
            else:
                surrounding_edge_count += 1

        if enwiki:
            surface = wikipedia_surface(enwiki, args.max_wikipedia_links, args.timeout)
            wikipedia_pages[qid] = surface
            first_title = str(surface.get("first_mainspace_link_candidate", ""))
            if first_title:
                first_qid, canonical_title = qid_for_title(first_title, args.timeout)
                receipt = {
                    "from_qid": qid,
                    "from_title": enwiki,
                    "candidate_title": canonical_title or first_title,
                    "candidate_qid": first_qid,
                    "edge_kind": "current-first-mainspace-link-candidate",
                    "ibrahim_parser_equivalence_paid": False,
                    "historical_snapshot_identity_paid": False,
                    "semantic_promotion": False,
                }
                first_link_candidates.append(receipt)
                if first_qid and depth < args.max_depth:
                    queue.append((first_qid, depth + 1, seed_id, "wikipedia-first-link-candidate"))
                    first_link_follow_count += 1

    graph = {
        "schema": SCHEMA,
        "source_world_model_id": world.get("model_id", ""),
        "seed_receipts": seed_receipts,
        "nodes": sorted(nodes.values(), key=lambda x: (int(x.get("depth", 0)), str(x.get("node_id", "")))),
        "item_property_edges": edges,
        "wikipedia_pages": wikipedia_pages,
        "first_link_candidates": first_link_candidates,
        "routing_policy": {
            "wikidata_identity_before_broad_web": True,
            "wikidata_properties_before_broad_web": True,
            "parent_part_surrounding_before_broad_web": True,
            "wikipedia_related_categories_before_broad_web": True,
            "current_first_link_candidate_before_broad_web": True,
            "ibrahim_exact_historical_parser_claimed": False,
            "broad_snowball_after_wikimedia_residual": True,
            "lexical_search_promotes_identity": False,
        },
        "summary": {
            "input_seed_count": len(seeds),
            "unresolved_seed_count": unresolved_seed_count,
            "qid_node_count": len(nodes),
            "item_property_edge_count": len(edges),
            "parent_edge_count": parent_edge_count,
            "surrounding_or_related_edge_count": surrounding_edge_count,
            "wikipedia_page_count": len(wikipedia_pages),
            "first_link_candidate_count": len(first_link_candidates),
            "first_link_follow_count": first_link_follow_count,
        },
        "candidate_only": True,
        "semantic_promotion": False,
    }

    out = deepcopy(world)
    out.setdefault("external_graph_views", []).append({
        "graph_view_id": SCHEMA,
        "graph_kind": "wikimedia-first-world-acquisition",
        "status": "candidate",
        "sidecar": str(args.output_graph),
        "candidate_only": True,
        "semantic_promotion": False,
    })
    out.setdefault("update_rules", []).append({
        "rule_id": "wikimedia-first-before-broad-snowball-v1",
        "rule_kind": "world_acquisition_order",
        "description": "When additional world context is required, try Wikidata identity/properties and Wikipedia related/parent/surrounding/current-first-link candidate traversal before broader Snowball acquisition; retain residuals when these are insufficient.",
        "semantic_promotion": False,
    })
    metadata = out.setdefault("metadata", {})
    metadata["wikimedia_world_follow"] = {
        "schema": SCHEMA,
        "sidecar": str(args.output_graph),
        "qid_nodes": len(nodes),
        "property_edges": len(edges),
        "first_link_candidates": len(first_link_candidates),
        "ibrahim_parser_equivalence_paid": False,
        "historical_snapshot_identity_paid": False,
        "broad_snowball_after_wikimedia_residual": True,
        "candidate_only": True,
        "semantic_promotion": False,
    }
    metadata["semantic_promotion"] = False
    metadata["candidate_only"] = True

    args.output_graph.parent.mkdir(parents=True, exist_ok=True)
    args.output_model.parent.mkdir(parents=True, exist_ok=True)
    args.output_graph.write_text(json.dumps(graph, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    args.output_model.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    print(
        "SLR_WIKIMEDIA_WORLD_FOLLOW_RECEIPT "
        f"schema={SCHEMA} seeds={len(seeds)} unresolved_seeds={unresolved_seed_count} "
        f"qid_nodes={len(nodes)} property_edges={len(edges)} parent_edges={parent_edge_count} "
        f"surrounding_related_edges={surrounding_edge_count} wikipedia_pages={len(wikipedia_pages)} "
        f"first_link_candidates={len(first_link_candidates)} first_link_followed={first_link_follow_count} "
        "wikimedia_before_broad_snowball=true ibrahim_exact=false lexical_search_promotes_identity=false "
        "candidate_only=true semantic_promotion=false",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
