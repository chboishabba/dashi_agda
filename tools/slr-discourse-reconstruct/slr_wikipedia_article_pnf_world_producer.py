#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from typing import Any

SCHEMA = "slr-wikipedia-article-pnf-world-producer-v1"
PRODUCER_ABI = "sensiblaw-integrated-semantic-producer-compatible-v1"
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
ROLE_DEPS = {
    "subject": {"nsubj", "nsubj:pass", "csubj", "csubj:pass", "expl"},
    "object": {"obj", "dobj", "iobj", "pobj", "obl"},
    "negation": {"neg"},
    "auxiliary": {"aux", "aux:pass", "auxpass", "cop"},
    "clause": {"acl", "advcl", "ccomp", "xcomp", "relcl"},
    "coordination": {"conj", "cc"},
}
ROLE_NAMES = ("subject", "object", "predicate", "negation", "auxiliary", "clause", "coordination")


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def cache_key(url: str) -> str:
    return sha256_text(url)


def query_url(base: str, params: dict[str, Any]) -> str:
    p = {k: str(v) for k, v in params.items()}
    p.setdefault("format", "json")
    p.setdefault("formatversion", "2")
    return base + "?" + urllib.parse.urlencode(p)


def api_get(url: str, cache_dir: Path, timeout: float, retries: int) -> tuple[dict[str, Any], bool]:
    cache_dir.mkdir(parents=True, exist_ok=True)
    path = cache_dir / f"{cache_key(url)}.json"
    if path.exists():
        return json.loads(path.read_text(encoding="utf-8")), True
    delay = 2.0
    for attempt in range(retries + 1):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "DASHI-SLR-ArticlePNF/1.0"})
            with urllib.request.urlopen(req, timeout=timeout) as response:
                payload = json.loads(response.read().decode("utf-8"))
            path.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")
            return payload, False
        except urllib.error.HTTPError as exc:
            if exc.code not in {429, 502, 503, 504} or attempt >= retries:
                raise
            retry_after = exc.headers.get("Retry-After")
            wait = float(retry_after) if retry_after and retry_after.isdigit() else delay
            time.sleep(min(wait, 60.0))
            delay = min(delay * 2.0, 60.0)
    raise RuntimeError("unreachable")


class _PlainTextHTML(HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.parts: list[str] = []
        self.skip_depth = 0

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        if tag in {"style", "script", "table", "math"}:
            self.skip_depth += 1
        elif tag in {"p", "li", "h1", "h2", "h3", "h4", "br"} and not self.skip_depth:
            self.parts.append("\n")

    def handle_endtag(self, tag: str) -> None:
        if tag in {"style", "script", "table", "math"} and self.skip_depth:
            self.skip_depth -= 1
        elif tag in {"p", "li", "h1", "h2", "h3", "h4"} and not self.skip_depth:
            self.parts.append("\n")

    def handle_data(self, data: str) -> None:
        if not self.skip_depth:
            self.parts.append(data)


def html_to_plaintext(html: str) -> str:
    parser = _PlainTextHTML()
    parser.feed(html)
    text = "".join(parser.parts)
    text = re.sub(r"[ \t]+", " ", text)
    text = re.sub(r"\n\s*\n+", "\n\n", text)
    return text.strip()


def article_manifestation(*, qid: str, language: str, title: str, pageid: int, revid: int,
                          revision_timestamp: str, revision_sha1: str, text: str) -> dict[str, Any]:
    return {
        "manifestation_kind": "wikipedia-revision-text",
        "qid": qid,
        "language": language,
        "title": title,
        "pageid": int(pageid),
        "revision_id": int(revid),
        "revision_timestamp": revision_timestamp,
        "revision_sha1": revision_sha1,
        "source_text_sha256": sha256_text(text),
        "character_count": len(text),
        "revision_pinned": bool(revid > 0 and revision_timestamp),
        "producer_abi": PRODUCER_ABI,
        "article_text_creates_claim_truth": False,
        "candidate_only": True,
        "semantic_promotion": False,
    }


def source_unit_manifestation(*, source_unit_ref: str, source_kind: str, language: str,
                              revision_ref: str, text: str) -> dict[str, Any]:
    return {
        "manifestation_kind": "source-unit-text",
        "source_unit_ref": source_unit_ref,
        "source_kind": source_kind,
        "language": language,
        "revision_ref": revision_ref,
        "source_text_sha256": sha256_text(text),
        "character_count": len(text),
        "producer_abi": PRODUCER_ABI,
        "source_unit_text_creates_migration_truth": False,
        "candidate_only": True,
        "semantic_promotion": False,
    }


def _role_counts(rows: list[dict[str, Any]]) -> dict[str, int]:
    counts = {name: 0 for name in ROLE_NAMES}
    for row in rows:
        dep = str(row.get("dep", "")).lower()
        if dep == "root":
            counts["predicate"] += 1
        for role, deps in ROLE_DEPS.items():
            if dep in deps:
                counts[role] += 1
    return counts


def pnf_candidate_from_dependency_rows(rows: list[dict[str, Any]], *, document_ref: str,
                                       sentence_index: int, sentence_start: int,
                                       sentence_end: int, sentence_sha256: str) -> dict[str, Any]:
    subjects = [str(r.get("text", "")) for r in rows if str(r.get("dep", "")).lower() in ROLE_DEPS["subject"]]
    objects = [str(r.get("text", "")) for r in rows if str(r.get("dep", "")).lower() in ROLE_DEPS["object"]]
    predicates = [str(r.get("lemma", r.get("text", ""))) for r in rows if str(r.get("dep", "")).lower() == "root"]
    auxiliaries = [str(r.get("lemma", r.get("text", ""))) for r in rows if str(r.get("dep", "")).lower() in ROLE_DEPS["auxiliary"]]
    counts = _role_counts(rows)
    identity_payload = f"{document_ref}|{sentence_index}|{sentence_start}|{sentence_end}|{sentence_sha256}"
    claim_id = "pnf-candidate:" + sha256_text(identity_payload)
    return {
        "claim_candidate_id": claim_id,
        "document_ref": document_ref,
        "sentence_index": int(sentence_index),
        "source_span_start": int(sentence_start),
        "source_span_end": int(sentence_end),
        "sentence_text_sha256": sentence_sha256,
        "subject_terms": subjects,
        "predicate_lemmas": predicates,
        "object_terms": objects,
        "auxiliary_lemmas": auxiliaries,
        "negated": counts["negation"] > 0,
        "role_counts": counts,
        "dependency_rows": rows,
        "producer_contract": "sl.pnf.integrated_semantic_producer.v0_1",
        "sub_executor_ref": "spacy-dependency-to-candidate-pnf",
        "operation_kind": "observation",
        "parser_output_is_ontology_truth": False,
        "claim_truth_promoted": False,
        "candidate_only": True,
        "semantic_promotion": False,
    }


def qid_pnf_weld_candidate(*, qid: str, document_ref: str, claim_candidate_id: str) -> dict[str, Any]:
    return {
        "weld_candidate_id": "qid-pnf-weld:" + sha256_text(f"{qid}|{document_ref}|{claim_candidate_id}"),
        "qid": qid,
        "document_ref": document_ref,
        "claim_candidate_id": claim_candidate_id,
        "surface_qid_identity_paid": True,
        "span_entity_identity_paid": False,
        "qid_property_weld_paid": False,
        "claim_semantic_equivalence_paid": False,
        "claim_truth_promoted": False,
        "candidate_only": True,
        "semantic_promotion": False,
    }


def parse_with_spacy(text: str, language: str, model_name: str | None = None) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    import spacy  # type: ignore

    model = model_name or MODEL_BY_LANG.get(language, f"{language}_core_news_sm")
    nlp = spacy.load(model)
    if "parser" not in nlp.pipe_names:
        raise RuntimeError(f"trained dependency parser required for semantic producer: {language}:{model}")
    doc = nlp(text)
    document_ref = "pending"
    sentence_rows: list[dict[str, Any]] = []
    for sentence_index, sent in enumerate(doc.sents):
        rows = [
            {
                "i": int(tok.i - sent.start),
                "text": tok.text,
                "lemma": tok.lemma_,
                "dep": tok.dep_,
                "head_i": int(tok.head.i - sent.start),
                "idx": int(tok.idx),
                "pos": tok.pos_,
                "tag": tok.tag_,
            }
            for tok in sent
        ]
        sentence_rows.append({
            "sentence_index": sentence_index,
            "sentence_start": int(sent.start_char),
            "sentence_end": int(sent.end_char),
            "sentence_sha256": sha256_text(sent.text),
            "dependency_rows": rows,
        })
    return sentence_rows, {
        "parser_backend": "spacy-trained",
        "parser_model": model,
        "spacy_version": getattr(spacy, "__version__", ""),
        "dependency_capable": True,
        "token_count": len(doc),
        "sentence_count": len(sentence_rows),
        "document_ref_placeholder": document_ref,
    }


def fetch_qid_sitelinks(qids: list[str], languages: list[str], cache_dir: Path,
                        timeout: float, retries: int) -> tuple[dict[str, dict[str, str]], int, int]:
    if not qids:
        return {}, 0, 0
    url = query_url(WIKIDATA_API, {"action": "wbgetentities", "ids": "|".join(qids), "props": "sitelinks"})
    payload, hit = api_get(url, cache_dir, timeout, retries)
    out: dict[str, dict[str, str]] = {}
    for qid in qids:
        entity = (payload.get("entities") or {}).get(qid) or {}
        raw = entity.get("sitelinks") or {}
        per: dict[str, str] = {}
        for lang in languages:
            key = "simplewiki" if lang == "simple" else f"{lang}wiki"
            title = str((raw.get(key) or {}).get("title", ""))
            if title:
                per[lang] = title
        out[qid] = per
    return out, 1 if hit else 0, 0 if hit else 1


def fetch_revision_article(language: str, title: str, cache_dir: Path,
                           timeout: float, retries: int) -> tuple[dict[str, Any], str, int, int]:
    host_lang = "simple" if language == "simple" else language
    base = f"https://{host_lang}.wikipedia.org/w/api.php"
    rev_url = query_url(base, {
        "action": "query", "prop": "revisions", "rvprop": "ids|timestamp|sha1",
        "titles": title, "redirects": 1,
    })
    rev_payload, hit1 = api_get(rev_url, cache_dir, timeout, retries)
    pages = ((rev_payload.get("query") or {}).get("pages") or [])
    if not pages:
        raise RuntimeError(f"no Wikipedia page for {language}:{title}")
    page = pages[0]
    revisions = page.get("revisions") or []
    if not revisions:
        raise RuntimeError(f"no revision for {language}:{title}")
    rev = revisions[0]
    revid = int(rev.get("revid", -1))
    parse_url = query_url(base, {"action": "parse", "oldid": revid, "prop": "text"})
    parse_payload, hit2 = api_get(parse_url, cache_dir, timeout, retries)
    html = str(((parse_payload.get("parse") or {}).get("text") or ""))
    text = html_to_plaintext(html)
    meta = {
        "title": str(page.get("title", title)),
        "pageid": int(page.get("pageid", -1)),
        "revid": revid,
        "revision_timestamp": str(rev.get("timestamp", "")),
        "revision_sha1": str(rev.get("sha1", "")),
    }
    return meta, text, int(hit1) + int(hit2), int(not hit1) + int(not hit2)


def selected_qids_from_route_plan(plan: dict[str, Any]) -> list[str]:
    qids: list[str] = []
    for row in plan.get("selected_route_actions") or []:
        if not isinstance(row, dict):
            continue
        qid = str(row.get("target_qid", "")).strip()
        if qid and qid not in qids:
            qids.append(qid)
    return qids


def build_article_producer(route_plan: dict[str, Any], *, languages: list[str], cache_dir: Path,
                           timeout: float, retries: int) -> dict[str, Any]:
    qids = selected_qids_from_route_plan(route_plan)
    titles, cache_hits, network_requests = fetch_qid_sitelinks(qids, languages, cache_dir, timeout, retries)
    manifestations: list[dict[str, Any]] = []
    candidates: list[dict[str, Any]] = []
    welds: list[dict[str, Any]] = []
    parser_receipts: list[dict[str, Any]] = []
    missing_surfaces: list[dict[str, Any]] = []

    for qid in qids:
        for language in languages:
            title = (titles.get(qid) or {}).get(language, "")
            if not title:
                missing_surfaces.append({"qid": qid, "language": language, "reason": "missing-sitelink"})
                continue
            meta, text, hits, net = fetch_revision_article(language, title, cache_dir, timeout, retries)
            cache_hits += hits
            network_requests += net
            manifestation = article_manifestation(
                qid=qid,
                language=language,
                title=meta["title"],
                pageid=meta["pageid"],
                revid=meta["revid"],
                revision_timestamp=meta["revision_timestamp"],
                revision_sha1=meta["revision_sha1"],
                text=text,
            )
            manifestations.append(manifestation)
            document_ref = f"wiki:{qid}:{language}:{meta['revid']}"
            sentence_rows, receipt = parse_with_spacy(text, language)
            receipt.update({
                "document_ref": document_ref,
                "source_text_sha256": manifestation["source_text_sha256"],
                "producer_abi": PRODUCER_ABI,
                "parser_output_is_promotion_authority": False,
            })
            parser_receipts.append(receipt)
            for row in sentence_rows:
                candidate = pnf_candidate_from_dependency_rows(
                    row["dependency_rows"],
                    document_ref=document_ref,
                    sentence_index=row["sentence_index"],
                    sentence_start=row["sentence_start"],
                    sentence_end=row["sentence_end"],
                    sentence_sha256=row["sentence_sha256"],
                )
                candidates.append(candidate)
                welds.append(qid_pnf_weld_candidate(
                    qid=qid,
                    document_ref=document_ref,
                    claim_candidate_id=candidate["claim_candidate_id"],
                ))

    return {
        "schema": SCHEMA,
        "producer_abi": PRODUCER_ABI,
        "source_route_plan_schema": route_plan.get("schema", ""),
        "article_manifestations": manifestations,
        "parser_receipts": parser_receipts,
        "pnf_candidates": candidates,
        "qid_pnf_weld_candidates": welds,
        "missing_surfaces": missing_surfaces,
        "summary": {
            "selected_qids": len(qids),
            "article_manifestations": len(manifestations),
            "parser_receipts": len(parser_receipts),
            "pnf_candidates": len(candidates),
            "qid_pnf_weld_candidates": len(welds),
            "missing_surfaces": len(missing_surfaces),
            "cache_hits": cache_hits,
            "network_requests": network_requests,
        },
        "spacy_dependency_surface_explicit": True,
        "pnf_candidate_surface_explicit": True,
        "surface_qid_identity_does_not_pay_span_entity_identity": True,
        "article_text_creates_claim_truth": False,
        "parser_output_creates_ontology_truth": False,
        "candidate_only": True,
        "semantic_promotion": False,
    }


def self_check() -> int:
    rows = [
        {"i": 0, "text": "A", "lemma": "a", "dep": "nsubj", "head_i": 1, "idx": 0},
        {"i": 1, "text": "is", "lemma": "be", "dep": "ROOT", "head_i": 1, "idx": 2},
        {"i": 2, "text": "B", "lemma": "b", "dep": "attr", "head_i": 1, "idx": 5},
    ]
    c = pnf_candidate_from_dependency_rows(rows, document_ref="wiki:Q1:en:1", sentence_index=0,
                                           sentence_start=0, sentence_end=6, sentence_sha256="x")
    assert c["role_counts"]["subject"] == 1
    assert c["role_counts"]["predicate"] == 1
    assert c["parser_output_is_ontology_truth"] is False
    w = qid_pnf_weld_candidate(qid="Q1", document_ref="wiki:Q1:en:1", claim_candidate_id=c["claim_candidate_id"])
    assert w["surface_qid_identity_paid"] is True
    assert w["span_entity_identity_paid"] is False
    print(
        "SLR_WIKIPEDIA_ARTICLE_PNF_WORLD_PRODUCER_SELF_CHECK "
        f"schema={SCHEMA} passed=true spacy_dependency_surface_explicit=true pnf_candidate_surface_explicit=true "
        "surface_qid_identity_does_not_pay_span_entity_identity=true article_text_creates_claim_truth=false "
        "parser_output_creates_ontology_truth=false candidate_only=true semantic_promotion=false",
        file=sys.stderr,
    )
    return 0


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--route-plan", type=Path)
    p.add_argument("--output", type=Path)
    p.add_argument("--cache-dir", type=Path)
    p.add_argument("--languages", default="en")
    p.add_argument("--timeout", type=float, default=20.0)
    p.add_argument("--retries", type=int, default=5)
    p.add_argument("--self-check", action="store_true")
    return p.parse_args()


def main() -> int:
    args = parse_args()
    if args.self_check:
        return self_check()
    if not args.route_plan or not args.output or not args.cache_dir:
        raise SystemExit("--route-plan, --output and --cache-dir are required")
    route_plan = json.loads(args.route_plan.read_text(encoding="utf-8"))
    languages = [x.strip() for x in args.languages.split(",") if x.strip()]
    payload = build_article_producer(route_plan, languages=languages, cache_dir=args.cache_dir,
                                     timeout=args.timeout, retries=args.retries)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    s = payload["summary"]
    print(
        "SLR_WIKIPEDIA_ARTICLE_PNF_WORLD_PRODUCER_RECEIPT "
        f"schema={SCHEMA} selected_qids={s['selected_qids']} article_manifestations={s['article_manifestations']} "
        f"pnf_candidates={s['pnf_candidates']} qid_pnf_weld_candidates={s['qid_pnf_weld_candidates']} "
        f"missing_surfaces={s['missing_surfaces']} cache_hits={s['cache_hits']} network_requests={s['network_requests']} "
        "spacy_dependency_surface_explicit=true pnf_candidate_surface_explicit=true "
        "surface_qid_identity_does_not_pay_span_entity_identity=true article_text_creates_claim_truth=false "
        "parser_output_creates_ontology_truth=false candidate_only=true semantic_promotion=false",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
