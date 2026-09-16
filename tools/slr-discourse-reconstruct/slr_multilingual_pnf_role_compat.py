#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import Counter
from pathlib import Path
from typing import Any

SCHEMA = "slr-multilingual-pnf-role-compat-v1"
MODEL_BY_LANG = {
    "en": "en_core_web_sm",
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


def load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise SystemExit(f"expected JSON object: {path}")
    return value


def cache_key(url: str) -> str:
    return hashlib.sha256(url.encode("utf-8")).hexdigest()


def query_url(base: str, params: dict[str, Any]) -> str:
    import urllib.parse
    p = {k: str(v) for k, v in params.items()}
    p.setdefault("format", "json")
    p.setdefault("formatversion", "2")
    return base + "?" + urllib.parse.urlencode(p)


def cached_intro(language: str, title: str, cache_dir: Path) -> str:
    base = f"https://{language}.wikipedia.org/w/api.php"
    url = query_url(base, {
        "action": "query",
        "prop": "extracts",
        "exintro": 1,
        "explaintext": 1,
        "redirects": 1,
        "titles": title,
    })
    path = cache_dir / f"{cache_key(url)}.json"
    if not path.exists():
        raise SystemExit(f"missing cached multilingual surface for {language}:{title}: {path}")
    payload = json.loads(path.read_text(encoding="utf-8"))
    pages = ((payload.get("query") or {}).get("pages") or [])
    if not pages:
        return ""
    return str(pages[0].get("extract", ""))


def normalized_dep(dep: str) -> str:
    return dep.strip().lower()


def parse_signature(text: str, language: str, expected_model: str) -> dict[str, Any]:
    import spacy  # type: ignore

    model = MODEL_BY_LANG.get(language, expected_model)
    nlp = spacy.load(model)
    if "parser" not in nlp.pipe_names:
        raise SystemExit(f"trained parser missing for {language}:{model}")
    doc = nlp(text)

    counts = Counter({name: 0 for name in ROLE_NAMES})
    dep_counts: Counter[str] = Counter()
    sentence_count = 0
    root_count = 0
    for sent in doc.sents:
        sentence_count += 1
        for tok in sent:
            dep = normalized_dep(tok.dep_)
            dep_counts[dep] += 1
            if dep == "root":
                counts["predicate"] += 1
                root_count += 1
            for role, deps in ROLE_DEPS.items():
                if dep in deps:
                    counts[role] += 1

    active = [name for name in ROLE_NAMES if counts[name] > 0]
    denom = max(len(doc), 1)
    density_milli = {name: (counts[name] * 1000) // denom for name in ROLE_NAMES}
    return {
        "token_count": len(doc),
        "sentence_count": sentence_count,
        "root_count": root_count,
        "role_counts": dict(counts),
        "role_density_milli": density_milli,
        "active_roles": active,
        "all_core_role_families_represented": all(counts[name] > 0 for name in ("subject", "predicate", "object")),
        "dependency_label_inventory": sorted(dep_counts),
        "parser_model": model,
        "spacy_version": getattr(spacy, "__version__", ""),
    }


def jaccard(left: set[str], right: set[str]) -> int:
    union = left | right
    if not union:
        return 1000
    return (1000 * len(left & right)) // len(union)


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--multilingual-compat", type=Path, required=True)
    p.add_argument("--cache-dir", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    return p.parse_args()


def main() -> int:
    args = parse_args()
    compat = load(args.multilingual_compat)
    if compat.get("schema") != "slr-multilingual-wikimedia-parser-compat-v1":
        raise SystemExit(f"unexpected multilingual schema: {compat.get('schema')!r}")
    if bool(compat.get("semantic_promotion", False)):
        raise SystemExit("refusing semantically promoted multilingual input")

    rows: list[dict[str, Any]] = []
    by_qid: dict[str, list[dict[str, Any]]] = {}
    for surface in compat.get("surfaces") or []:
        if not isinstance(surface, dict):
            continue
        if not bool(surface.get("trained_model_loaded", False)) or not bool(surface.get("dependency_capable", False)):
            raise SystemExit("PNF role compatibility requires trained dependency-capable surfaces")
        qid = str(surface.get("qid", ""))
        lang = str(surface.get("language", ""))
        title = str(surface.get("wikipedia_title", ""))
        model = str(surface.get("parser_model", ""))
        text = cached_intro(lang, title, args.cache_dir)
        sig = parse_signature(text, lang, model)
        row = {
            "qid": qid,
            "language": lang,
            "wikipedia_title": title,
            "source_text_sha256": str(surface.get("text_sha256", "")),
            **sig,
            "same_qid_identity_paid": True,
            "sentence_alignment_paid": False,
            "translation_equivalence_paid": False,
            "claim_semantic_equivalence_paid": False,
            "candidate_only": True,
            "semantic_promotion": False,
        }
        rows.append(row)
        by_qid.setdefault(qid, []).append(row)

    pairs: list[dict[str, Any]] = []
    all_core_surfaces = sum(1 for r in rows if r["all_core_role_families_represented"])
    for qid, surfaces in sorted(by_qid.items()):
        for i in range(len(surfaces)):
            for j in range(i + 1, len(surfaces)):
                a, b = surfaces[i], surfaces[j]
                aset = set(a["active_roles"])
                bset = set(b["active_roles"])
                common = sorted(aset & bset)
                pairs.append({
                    "qid": qid,
                    "left_language": a["language"],
                    "right_language": b["language"],
                    "shared_qid_identity_paid": True,
                    "active_role_jaccard_milli": jaccard(aset, bset),
                    "common_active_roles": common,
                    "core_role_carrier_compatible": all(x in common for x in ("subject", "predicate", "object")),
                    "sentence_alignment_paid": False,
                    "translation_equivalence_paid": False,
                    "claim_semantic_equivalence_paid": False,
                    "candidate_only": True,
                    "semantic_promotion": False,
                })

    core_pairs = sum(1 for p in pairs if p["core_role_carrier_compatible"])
    payload = {
        "schema": SCHEMA,
        "source_schema": compat.get("schema", ""),
        "surfaces": rows,
        "pairs": pairs,
        "summary": {
            "qids": len(by_qid),
            "surfaces": len(rows),
            "language_pairs": len(pairs),
            "surfaces_with_subject_predicate_object": all_core_surfaces,
            "pairs_with_core_role_carrier_compatibility": core_pairs,
        },
        "shared_qid_pays_entity_identity": True,
        "role_family_overlap_pays_translation_equivalence": False,
        "role_family_overlap_pays_sentence_alignment": False,
        "role_family_overlap_pays_claim_semantic_equivalence": False,
        "candidate_only": True,
        "semantic_promotion": False,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    s = payload["summary"]
    print(
        "SLR_MULTILINGUAL_PNF_ROLE_COMPAT_RECEIPT "
        f"schema={SCHEMA} qids={s['qids']} surfaces={s['surfaces']} language_pairs={s['language_pairs']} "
        f"surfaces_with_subject_predicate_object={s['surfaces_with_subject_predicate_object']} "
        f"pairs_with_core_role_carrier_compatibility={s['pairs_with_core_role_carrier_compatibility']} "
        "shared_qid_identity=true translation_equivalence=false sentence_alignment=false "
        "claim_semantic_equivalence=false candidate_only=true semantic_promotion=false",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
