#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from collections import defaultdict
from pathlib import Path
from typing import Any

SCHEMA = "slr-semantic-world-closure-v1"
WIKIDATA_API = "https://www.wikidata.org/w/api.php"


def load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise SystemExit(f"expected JSON object: {path}")
    return value


def query_url(base: str, params: dict[str, Any]) -> str:
    p = {k: str(v) for k, v in params.items()}
    p.setdefault("format", "json")
    p.setdefault("formatversion", "2")
    return base + "?" + urllib.parse.urlencode(p)


def cache_key(url: str) -> str:
    return hashlib.sha256(url.encode("utf-8")).hexdigest()


def api_get(url: str, cache_dir: Path, timeout: float, retries: int) -> dict[str, Any]:
    cache_dir.mkdir(parents=True, exist_ok=True)
    path = cache_dir / f"{cache_key(url)}.json"
    if path.exists():
        return json.loads(path.read_text(encoding="utf-8"))
    delay = 2.0
    for attempt in range(retries + 1):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "DASHI-SLR-SemanticClosure/1.0"})
            with urllib.request.urlopen(req, timeout=timeout) as response:
                payload = json.loads(response.read().decode("utf-8"))
            path.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")
            return payload
        except urllib.error.HTTPError as exc:
            if exc.code not in {429, 502, 503, 504} or attempt >= retries:
                raise
            retry_after = exc.headers.get("Retry-After")
            wait = float(retry_after) if retry_after and retry_after.isdigit() else delay
            time.sleep(min(wait, 60.0))
            delay = min(delay * 2.0, 60.0)
    raise RuntimeError("unreachable")


def atom_id(kind: str, *parts: str) -> str:
    return kind + ":" + ":".join(parts)


def root_qids(graph: dict[str, Any], multilingual: dict[str, Any] | None) -> list[str]:
    if multilingual:
        qids = [str(q) for q in multilingual.get("qids") or [] if str(q)]
        if qids:
            return list(dict.fromkeys(qids))
    out: list[str] = []
    for receipt in graph.get("seed_receipts") or []:
        if not isinstance(receipt, dict):
            continue
        for candidate in receipt.get("candidate_qids") or []:
            if isinstance(candidate, dict) and bool(candidate.get("identity_paid", False)):
                qid = str(candidate.get("id", ""))
                if qid and qid not in out:
                    out.append(qid)
    return out


def sitelinks(qids: list[str], languages: list[str], cache_dir: Path, timeout: float, retries: int) -> dict[str, dict[str, str]]:
    if not qids:
        return {}
    url = query_url(WIKIDATA_API, {
        "action": "wbgetentities",
        "ids": "|".join(qids),
        "props": "sitelinks",
    })
    data = api_get(url, cache_dir, timeout, retries)
    entities = data.get("entities") or {}
    result: dict[str, dict[str, str]] = {}
    for qid in qids:
        entity = entities.get(qid) or {}
        raw = entity.get("sitelinks") or {}
        per: dict[str, str] = {}
        for lang in languages:
            key = "simplewiki" if lang == "simple" else f"{lang}wiki"
            title = str((raw.get(key) or {}).get("title", ""))
            if title:
                per[lang] = title
        result[qid] = per
    return result


def linked_qids(language: str, title: str, cache_dir: Path, timeout: float, retries: int, max_links: int) -> list[str]:
    host_lang = "simple" if language == "simple" else language
    base = f"https://{host_lang}.wikipedia.org/w/api.php"
    url = query_url(base, {
        "action": "query",
        "generator": "links",
        "titles": title,
        "gplnamespace": 0,
        "gpllimit": max_links,
        "prop": "pageprops",
        "ppprop": "wikibase_item",
        "redirects": 1,
    })
    data = api_get(url, cache_dir, timeout, retries)
    qids: list[str] = []
    for page in ((data.get("query") or {}).get("pages") or []):
        if not isinstance(page, dict):
            continue
        qid = str(((page.get("pageprops") or {}).get("wikibase_item") or ""))
        if qid and qid.startswith("Q") and qid not in qids:
            qids.append(qid)
    return sorted(qids)


def graph_property_atoms(graph: dict[str, Any]) -> tuple[list[dict[str, Any]], dict[tuple[str, str], list[str]]]:
    atoms: list[dict[str, Any]] = []
    by_pair: dict[tuple[str, str], list[str]] = defaultdict(list)
    for edge in graph.get("item_property_edges") or []:
        if not isinstance(edge, dict):
            continue
        source = str(edge.get("source", ""))
        pid = str(edge.get("property_id", ""))
        target = str(edge.get("target", ""))
        if not (source and pid and target):
            continue
        aid = atom_id("wikidata-property", source, pid, target)
        atoms.append({
            "atom_id": aid,
            "kind": "wikidata-property",
            "subject_qid": source,
            "property_id": pid,
            "object_qid": target,
            "evidence_class": "reviewed-wikimedia-world-graph",
            "claim_truth_promoted": False,
        })
        by_pair[(source, target)].append(pid)
    atoms.sort(key=lambda a: a["atom_id"])
    return atoms, by_pair


def build_closure(graph: dict[str, Any], qids: list[str], languages: list[str], links_by_surface: dict[tuple[str, str], list[str]], titles: dict[str, dict[str, str]]) -> dict[str, Any]:
    property_atoms, property_by_pair = graph_property_atoms(graph)
    canonical: dict[str, dict[str, Any]] = {a["atom_id"]: a for a in property_atoms}
    observed: dict[str, set[str]] = {}
    evidence_surfaces: dict[str, list[str]] = defaultdict(list)
    surfaces: list[dict[str, Any]] = []

    for qid in qids:
        qid_atom = atom_id("qid", qid)
        canonical.setdefault(qid_atom, {
            "atom_id": qid_atom,
            "kind": "qid",
            "qid": qid,
            "evidence_class": "shared-qid-identity",
            "claim_truth_promoted": False,
        })
        for language in languages:
            title = (titles.get(qid) or {}).get(language, "")
            sid = f"{qid}:{language}"
            if not title:
                surfaces.append({
                    "surface_id": sid,
                    "qid": qid,
                    "language": language,
                    "status": "missing-sitelink",
                    "observed_atom_ids": [],
                    "candidate_only": True,
                    "semantic_promotion": False,
                })
                observed[sid] = set()
                continue
            atom_ids: set[str] = {qid_atom}
            evidence_surfaces[qid_atom].append(sid)
            for related in links_by_surface.get((qid, language), []):
                link_id = atom_id("wiki-link", qid, related)
                canonical.setdefault(link_id, {
                    "atom_id": link_id,
                    "kind": "wiki-link",
                    "subject_qid": qid,
                    "object_qid": related,
                    "evidence_class": "language-surface-mainspace-link",
                    "article_link_is_claim_truth": False,
                    "claim_truth_promoted": False,
                })
                atom_ids.add(link_id)
                evidence_surfaces[link_id].append(sid)
                for pid in property_by_pair.get((qid, related), []):
                    prop_id = atom_id("wikidata-property", qid, pid, related)
                    atom_ids.add(prop_id)
                    evidence_surfaces[prop_id].append(sid)
            observed[sid] = atom_ids
            surfaces.append({
                "surface_id": sid,
                "qid": qid,
                "language": language,
                "wikipedia_title": title,
                "status": "observed",
                "linked_qid_count": len(links_by_surface.get((qid, language), [])),
                "observed_atom_ids": sorted(atom_ids),
                "candidate_only": True,
                "semantic_promotion": False,
            })

    surface_closure = sorted(aid for aid, a in canonical.items() if a.get("kind") in {"qid", "wiki-link", "wikidata-property"} and evidence_surfaces.get(aid))
    gaps: list[dict[str, Any]] = []
    propagated: list[dict[str, Any]] = []
    for surface in surfaces:
        sid = surface["surface_id"]
        if surface["status"] != "observed":
            gaps.append({
                "surface_id": sid,
                "qid": surface["qid"],
                "language": surface["language"],
                "gap_kind": "missing-surface",
                "missing_atom_ids": [],
                "candidate_only": True,
                "semantic_promotion": False,
            })
            continue
        missing = [aid for aid in surface_closure if aid not in observed[sid] and (canonical[aid].get("subject_qid") in {None, surface["qid"]} or canonical[aid].get("qid") == surface["qid"])]
        gaps.append({
            "surface_id": sid,
            "qid": surface["qid"],
            "language": surface["language"],
            "gap_kind": "semantic-atom-gap",
            "missing_atom_ids": missing,
            "candidate_only": True,
            "semantic_promotion": False,
        })
        for aid in missing:
            propagated.append({
                "target_surface_id": sid,
                "target_language": surface["language"],
                "atom_id": aid,
                "source_surface_ids": sorted(set(evidence_surfaces.get(aid, []))),
                "available_to_target_consumer": True,
                "target_surface_asserted": False,
                "translation_equivalence_paid": False,
                "claim_semantic_equivalence_paid": False,
                "candidate_only": True,
                "semantic_promotion": False,
            })

    node_ids = {str(n.get("node_id", "")) for n in graph.get("nodes") or [] if isinstance(n, dict)}
    obligations: list[dict[str, Any]] = []
    for surface in surfaces:
        if surface["status"] == "missing-sitelink":
            obligations.append({
                "obligation_kind": "missing-language-surface",
                "qid": surface["qid"],
                "language": surface["language"],
                "routing_priority": "wikidata-sitelink-or-wikipedia-search-before-broad-snowball",
                "candidate_only": True,
            })
    related_targets = sorted({a.get("object_qid", "") for a in canonical.values() if a.get("kind") == "wiki-link"})
    for target in related_targets:
        if target and target not in node_ids:
            obligations.append({
                "obligation_kind": "follow-related-qid",
                "qid": target,
                "routing_priority": "wikidata-properties-then-wikipedia-ibrahim-follow",
                "candidate_only": True,
            })

    return {
        "canonical_atoms": [canonical[k] for k in sorted(canonical)],
        "surface_semantic_closure_atom_ids": surface_closure,
        "world_property_atom_ids": [a["atom_id"] for a in property_atoms],
        "surfaces": surfaces,
        "gaps": gaps,
        "propagated_views": propagated,
        "acquisition_obligations": obligations,
    }


def self_check() -> int:
    graph = {
        "schema": "slr-wikimedia-world-follow-v1",
        "nodes": [{"node_id": "Q1"}, {"node_id": "Q2"}],
        "item_property_edges": [{"source": "Q1", "property_id": "P1", "target": "Q2"}],
    }
    titles = {"Q1": {"en": "A", "fr": "A-fr"}}
    links = {("Q1", "en"): ["Q2"], ("Q1", "fr"): []}
    result = build_closure(graph, ["Q1"], ["en", "fr"], links, titles)
    prop = [p for p in result["propagated_views"] if p["target_surface_id"] == "Q1:fr"]
    assert prop, "expected propagated gap"
    assert all(p["target_surface_asserted"] is False for p in prop)
    assert all(p["semantic_promotion"] is False for p in prop)
    print("SLR_SEMANTIC_WORLD_CLOSURE_SELF_CHECK schema=slr-semantic-world-closure-v1 passed=true target_surface_asserted=false semantic_promotion=false", file=sys.stderr)
    return 0


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--graph", type=Path)
    p.add_argument("--multilingual-compat", type=Path)
    p.add_argument("--cache-dir", type=Path)
    p.add_argument("--output", type=Path)
    p.add_argument("--languages", default="en,es,fr,de,simple")
    p.add_argument("--max-links", type=int, default=60)
    p.add_argument("--timeout", type=float, default=20.0)
    p.add_argument("--retries", type=int, default=5)
    p.add_argument("--self-check", action="store_true")
    return p.parse_args()


def main() -> int:
    args = parse_args()
    if args.self_check:
        return self_check()
    if not all([args.graph, args.cache_dir, args.output]):
        raise SystemExit("--graph, --cache-dir and --output are required unless --self-check")
    graph = load(args.graph)
    if graph.get("schema") != "slr-wikimedia-world-follow-v1":
        raise SystemExit(f"unexpected graph schema: {graph.get('schema')!r}")
    multilingual = load(args.multilingual_compat) if args.multilingual_compat and args.multilingual_compat.exists() else None
    languages = [x.strip() for x in args.languages.split(",") if x.strip()]
    qids = root_qids(graph, multilingual)
    titles = sitelinks(qids, languages, args.cache_dir, args.timeout, args.retries)
    links_by_surface: dict[tuple[str, str], list[str]] = {}
    for qid in qids:
        for language, title in (titles.get(qid) or {}).items():
            links_by_surface[(qid, language)] = linked_qids(language, title, args.cache_dir, args.timeout, args.retries, args.max_links)
    closure = build_closure(graph, qids, languages, links_by_surface, titles)
    payload = {
        "schema": SCHEMA,
        "source_graph_schema": graph.get("schema", ""),
        "source_multilingual_schema": (multilingual or {}).get("schema", ""),
        "languages_requested": languages,
        "root_qids": qids,
        **closure,
        "summary": {
            "qids": len(qids),
            "surfaces": len(closure["surfaces"]),
            "observed_surfaces": sum(1 for s in closure["surfaces"] if s["status"] == "observed"),
            "simplewiki_surfaces": sum(1 for s in closure["surfaces"] if s["language"] == "simple" and s["status"] == "observed"),
            "canonical_atoms": len(closure["canonical_atoms"]),
            "surface_closure_atoms": len(closure["surface_semantic_closure_atom_ids"]),
            "semantic_gap_atoms": sum(len(g.get("missing_atom_ids") or []) for g in closure["gaps"]),
            "propagated_views": len(closure["propagated_views"]),
            "acquisition_obligations": len(closure["acquisition_obligations"]),
        },
        "propagation_rewrites_target_surface": False,
        "article_link_creates_claim_truth": False,
        "same_qid_creates_semantic_equivalence": False,
        "candidate_only": True,
        "semantic_promotion": False,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    s = payload["summary"]
    print(
        "SLR_SEMANTIC_WORLD_CLOSURE_RECEIPT "
        f"schema={SCHEMA} qids={s['qids']} surfaces={s['surfaces']} observed_surfaces={s['observed_surfaces']} "
        f"simplewiki_surfaces={s['simplewiki_surfaces']} canonical_atoms={s['canonical_atoms']} "
        f"surface_closure_atoms={s['surface_closure_atoms']} semantic_gap_atoms={s['semantic_gap_atoms']} "
        f"propagated_views={s['propagated_views']} acquisition_obligations={s['acquisition_obligations']} "
        "target_surface_asserted=false article_link_creates_claim_truth=false same_qid_semantic_equivalence=false "
        "candidate_only=true semantic_promotion=false",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
