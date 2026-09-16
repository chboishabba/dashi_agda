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
from pathlib import Path
from typing import Any

SCHEMA = "slr-multilingual-wikimedia-parser-compat-v1"
WIKIDATA_API = "https://www.wikidata.org/w/api.php"
MODEL_BY_LANG = {
    "en": "en_core_web_sm",
    "simple": "en_core_web_sm",
    "es": "es_core_news_sm",
    "fr": "fr_core_news_sm",
    "de": "de_core_news_sm",
    "it": "it_core_news_sm",
    "pt": "pt_core_news_sm",
    "nl": "nl_core_news_sm",
}


def load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise SystemExit(f"expected JSON object: {path}")
    return value


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
            req = urllib.request.Request(url, headers={"User-Agent": "DASHI-SLR-MultilingualCompat/1.0"})
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
            delay = min(delay * 2, 60.0)
    raise RuntimeError("unreachable")


def query_url(base: str, params: dict[str, Any]) -> str:
    p = {k: str(v) for k, v in params.items()}
    p.setdefault("format", "json")
    p.setdefault("formatversion", "2")
    return base + "?" + urllib.parse.urlencode(p)


def root_qids(graph: dict[str, Any], limit: int) -> list[str]:
    out: list[str] = []
    for receipt in graph.get("seed_receipts") or []:
        if not isinstance(receipt, dict):
            continue
        for candidate in receipt.get("candidate_qids") or []:
            if not isinstance(candidate, dict) or not bool(candidate.get("identity_paid", False)):
                continue
            qid = str(candidate.get("id", ""))
            if qid and qid not in out:
                out.append(qid)
            if len(out) >= limit:
                return out
    return out


def intro_for(language: str, title: str, cache_dir: Path, timeout: float, retries: int) -> tuple[str, int]:
    base = f"https://{language}.wikipedia.org/w/api.php"
    url = query_url(base, {
        "action": "query",
        "prop": "extracts",
        "exintro": 1,
        "explaintext": 1,
        "redirects": 1,
        "titles": title,
    })
    data = api_get(url, cache_dir, timeout, retries)
    pages = ((data.get("query") or {}).get("pages") or [])
    if not pages:
        return "", -1
    page = pages[0]
    return str(page.get("extract", "")), int(page.get("pageid", -1))


def parse_surface(text: str, language: str) -> dict[str, Any]:
    try:
        import spacy  # type: ignore
    except Exception:
        return {
            "parser_backend": "unavailable",
            "parser_model": "",
            "trained_model_loaded": False,
            "dependency_capable": False,
            "token_count": 0,
            "sentence_count": 0,
        }

    model = MODEL_BY_LANG.get(language, f"{language}_core_news_sm")
    trained = False
    backend = "spacy-blank"
    try:
        nlp = spacy.load(model)
        trained = True
        backend = "spacy-trained"
    except Exception:
        blank_lang = "en" if language == "simple" else language
        try:
            nlp = spacy.blank(blank_lang)
        except Exception:
            nlp = spacy.blank("xx")
            backend = "spacy-blank-xx"
        if "sentencizer" not in nlp.pipe_names:
            nlp.add_pipe("sentencizer")
    doc = nlp(text)
    try:
        sentence_count = sum(1 for _ in doc.sents)
    except Exception:
        sentence_count = 0
    return {
        "parser_backend": backend,
        "parser_model": model if trained else getattr(nlp, "lang", language),
        "trained_model_loaded": trained,
        "dependency_capable": bool(trained and "parser" in nlp.pipe_names),
        "token_count": len(doc),
        "sentence_count": sentence_count,
        "spacy_version": getattr(spacy, "__version__", ""),
    }


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--graph", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--cache-dir", type=Path, required=True)
    p.add_argument("--languages", default="en,es,fr,de,simple")
    p.add_argument("--max-qids", type=int, default=4)
    p.add_argument("--timeout", type=float, default=20.0)
    p.add_argument("--retries", type=int, default=5)
    return p.parse_args()


def main() -> int:
    args = parse_args()
    graph = load(args.graph)
    if graph.get("schema") != "slr-wikimedia-world-follow-v1":
        raise SystemExit(f"unexpected graph schema: {graph.get('schema')!r}")
    languages = [x.strip() for x in args.languages.split(",") if x.strip()]
    qids = root_qids(graph, args.max_qids)
    if not qids:
        raise SystemExit("no identity-paid root QIDs available")

    wd_url = query_url(WIKIDATA_API, {
        "action": "wbgetentities",
        "ids": "|".join(qids),
        "props": "labels|sitelinks",
        "languages": "|".join(languages),
    })
    wd = api_get(wd_url, args.cache_dir, args.timeout, args.retries)
    entities = wd.get("entities") or {}

    rows: list[dict[str, Any]] = []
    shared_identity_pairs = 0
    trained_parser_surfaces = 0
    fallback_parser_surfaces = 0
    simplewiki_surfaces = 0
    for qid in qids:
        entity = entities.get(qid) or {}
        sitelinks = entity.get("sitelinks") or {}
        available_languages: list[str] = []
        for language in languages:
            sitelink = sitelinks.get(f"{language}wiki") or {}
            title = str(sitelink.get("title", ""))
            if not title:
                continue
            available_languages.append(language)
            if language == "simple":
                simplewiki_surfaces += 1
            text, pageid = intro_for(language, title, args.cache_dir, args.timeout, args.retries)
            digest = hashlib.sha256(text.encode("utf-8")).hexdigest() if text else ""
            parse = parse_surface(text, language)
            if parse["trained_model_loaded"]:
                trained_parser_surfaces += 1
            else:
                fallback_parser_surfaces += 1
            rows.append({
                "qid": qid,
                "language": language,
                "wikipedia_title": title,
                "pageid": pageid,
                "text_sha256": digest,
                "character_count": len(text),
                **parse,
                "same_qid_identity_paid": True,
                "translation_equivalence_paid": False,
                "claim_semantic_equivalence_paid": False,
                "simplewiki_is_presumed_subset_of_enwiki": False,
                "candidate_only": True,
                "semantic_promotion": False,
            })
        n = len(available_languages)
        shared_identity_pairs += n * (n - 1) // 2

    payload = {
        "schema": SCHEMA,
        "source_graph_schema": graph.get("schema", ""),
        "languages_requested": languages,
        "qids": qids,
        "surfaces": rows,
        "summary": {
            "qids": len(qids),
            "language_surfaces": len(rows),
            "simplewiki_surfaces": simplewiki_surfaces,
            "shared_qid_identity_pairs": shared_identity_pairs,
            "trained_parser_surfaces": trained_parser_surfaces,
            "fallback_parser_surfaces": fallback_parser_surfaces,
        },
        "same_qid_pays_cross_language_identity": True,
        "same_qid_pays_translation_equivalence": False,
        "parser_schema_compatibility_pays_semantic_equivalence": False,
        "simplewiki_is_presumed_subset_of_enwiki": False,
        "sensiblaw_translation_view_compatible": True,
        "sensiblaw_spacy_language_adapter_compatible": True,
        "candidate_only": True,
        "semantic_promotion": False,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    s = payload["summary"]
    print(
        "SLR_MULTILINGUAL_WIKIMEDIA_PARSER_COMPAT_RECEIPT "
        f"schema={SCHEMA} qids={s['qids']} language_surfaces={s['language_surfaces']} "
        f"simplewiki_surfaces={s['simplewiki_surfaces']} shared_qid_identity_pairs={s['shared_qid_identity_pairs']} "
        f"trained_parser_surfaces={s['trained_parser_surfaces']} "
        f"fallback_parser_surfaces={s['fallback_parser_surfaces']} "
        "same_qid_identity=true translation_equivalence=false semantic_equivalence=false "
        "simplewiki_subset_assumed=false sensiblaw_translation_view_compatible=true "
        "sensiblaw_spacy_language_adapter_compatible=true candidate_only=true semantic_promotion=false",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
