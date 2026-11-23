#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys
from typing import Any

from slr_wikipedia_article_pnf_world_producer import (
    MODEL_BY_LANG,
    PRODUCER_ABI,
    pnf_candidate_from_dependency_rows,
    sha256_text,
    source_unit_manifestation,
)

SCHEMA = "slr-source-unit-pnf-batch-v1"
_NLP_CACHE: dict[str, Any] = {}


def _nlp(language: str):
    import spacy  # type: ignore
    model = MODEL_BY_LANG.get(language, f"{language}_core_news_sm")
    if model not in _NLP_CACHE:
        nlp = spacy.load(model)
        if "parser" not in nlp.pipe_names:
            raise RuntimeError(f"trained dependency parser required: {language}:{model}")
        _NLP_CACHE[model] = nlp
    return _NLP_CACHE[model], model, getattr(spacy, "__version__", "")


def _text_for_row(row: dict[str, Any], base_dir: Path) -> str:
    if isinstance(row.get("text"), str):
        return str(row["text"])
    text_path = str(row.get("text_path", "")).strip()
    if text_path:
        path = Path(text_path)
        if not path.is_absolute():
            path = base_dir / path
        return path.read_text(encoding="utf-8")
    raise ValueError("source unit requires text or text_path")


def process_source_unit(row: dict[str, Any], *, base_dir: Path) -> dict[str, Any]:
    source_unit_ref = str(row.get("source_unit_ref", "")).strip()
    source_kind = str(row.get("source_kind", "")).strip() or "source-unit"
    language = str(row.get("language", "en")).strip() or "en"
    revision_ref = str(row.get("revision_ref", "")).strip()
    if not source_unit_ref or not revision_ref:
        raise ValueError("source_unit_ref and revision_ref are required")
    text = _text_for_row(row, base_dir)
    manifestation = source_unit_manifestation(
        source_unit_ref=source_unit_ref,
        source_kind=source_kind,
        language=language,
        revision_ref=revision_ref,
        text=text,
    )
    nlp, model, spacy_version = _nlp(language)
    doc = nlp(text)
    document_ref = f"source-unit:{sha256_text(source_unit_ref + '|' + revision_ref)}"
    candidates: list[dict[str, Any]] = []
    for sentence_index, sent in enumerate(doc.sents):
        dep_rows = [
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
        candidates.append(pnf_candidate_from_dependency_rows(
            dep_rows,
            document_ref=document_ref,
            sentence_index=sentence_index,
            sentence_start=int(sent.start_char),
            sentence_end=int(sent.end_char),
            sentence_sha256=sha256_text(sent.text),
        ))
    return {
        "schema": "slr-source-unit-pnf-record-v1",
        "source_unit_ref": source_unit_ref,
        "source_kind": source_kind,
        "source_role": str(row.get("source_role", "unclassified")),
        "qid": str(row.get("qid", "")),
        "language": language,
        "revision_ref": revision_ref,
        "manifestation": manifestation,
        "parser_receipt": {
            "document_ref": document_ref,
            "parser_backend": "spacy-trained",
            "parser_model": model,
            "spacy_version": spacy_version,
            "dependency_capable": True,
            "token_count": len(doc),
            "sentence_count": len(candidates),
            "producer_abi": PRODUCER_ABI,
            "parser_output_is_promotion_authority": False,
        },
        "pnf_candidates": candidates,
        "summary": {
            "tokens": len(doc),
            "sentences": len(candidates),
            "pnf_candidates": len(candidates),
        },
        "source_role_creates_claim_truth": False,
        "parser_output_creates_ontology_truth": False,
        "candidate_only": True,
        "semantic_promotion": False,
    }


def stable_filename(source_unit_ref: str) -> str:
    return hashlib.sha256(source_unit_ref.encode("utf-8")).hexdigest() + ".json"


def run_batch(input_jsonl: Path, output_dir: Path, manifest_path: Path, *, max_source_units: int | None) -> dict[str, Any]:
    output_dir.mkdir(parents=True, exist_ok=True)
    base_dir = input_jsonl.parent
    count = 0
    total_sentences = 0
    total_candidates = 0
    languages: set[str] = set()
    with input_jsonl.open("r", encoding="utf-8") as src, manifest_path.open("w", encoding="utf-8") as manifest:
        for line_number, line in enumerate(src, start=1):
            if max_source_units is not None and count >= max_source_units:
                break
            if not line.strip():
                continue
            row = json.loads(line)
            if not isinstance(row, dict):
                raise ValueError(f"JSONL row {line_number} is not an object")
            record = process_source_unit(row, base_dir=base_dir)
            ref = str(record["source_unit_ref"])
            out_path = output_dir / stable_filename(ref)
            out_path.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
            s = record["summary"]
            manifest.write(json.dumps({
                "source_unit_ref": ref,
                "record_path": str(out_path),
                "language": record["language"],
                "revision_ref": record["revision_ref"],
                "source_text_sha256": record["manifestation"]["source_text_sha256"],
                "sentences": s["sentences"],
                "pnf_candidates": s["pnf_candidates"],
                "candidate_only": True,
                "semantic_promotion": False,
            }, sort_keys=True) + "\n")
            count += 1
            total_sentences += int(s["sentences"])
            total_candidates += int(s["pnf_candidates"])
            languages.add(str(record["language"]))
    return {
        "schema": SCHEMA,
        "source_units": count,
        "sentences": total_sentences,
        "pnf_candidates": total_candidates,
        "languages": sorted(languages),
        "models_loaded": len(_NLP_CACHE),
        "producer_abi": PRODUCER_ABI,
        "one_record_per_source_unit": True,
        "raw_text_embedded_in_manifest": False,
        "source_units_mutually_authoritative": False,
        "parser_output_creates_ontology_truth": False,
        "candidate_only": True,
        "semantic_promotion": False,
    }


def self_check() -> int:
    assert stable_filename("unit:a") == stable_filename("unit:a")
    assert stable_filename("unit:a") != stable_filename("unit:b")
    m = source_unit_manifestation(
        source_unit_ref="unit:nat:test", source_kind="wikidata-user-sandbox", language="en",
        revision_ref="r1", text="test",
    )
    assert m["producer_abi"] == PRODUCER_ABI
    assert m["source_unit_text_creates_migration_truth"] is False
    print(
        "SLR_SOURCE_UNIT_PNF_BATCH_SELF_CHECK "
        f"schema={SCHEMA} passed=true one_record_per_source_unit=true raw_text_embedded_in_manifest=false "
        "source_units_mutually_authoritative=false parser_output_creates_ontology_truth=false "
        "candidate_only=true semantic_promotion=false",
        file=sys.stderr,
    )
    return 0


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--input-jsonl", type=Path)
    p.add_argument("--output-dir", type=Path)
    p.add_argument("--manifest", type=Path)
    p.add_argument("--summary", type=Path)
    p.add_argument("--max-source-units", type=int)
    p.add_argument("--self-check", action="store_true")
    return p.parse_args()


def main() -> int:
    args = parse_args()
    if args.self_check:
        return self_check()
    if not args.input_jsonl or not args.output_dir or not args.manifest or not args.summary:
        raise SystemExit("--input-jsonl, --output-dir, --manifest and --summary are required")
    summary = run_batch(args.input_jsonl, args.output_dir, args.manifest, max_source_units=args.max_source_units)
    args.summary.parent.mkdir(parents=True, exist_ok=True)
    args.summary.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "SLR_SOURCE_UNIT_PNF_BATCH_RECEIPT "
        f"schema={SCHEMA} source_units={summary['source_units']} sentences={summary['sentences']} "
        f"pnf_candidates={summary['pnf_candidates']} languages={','.join(summary['languages'])} "
        f"models_loaded={summary['models_loaded']} one_record_per_source_unit=true "
        "raw_text_embedded_in_manifest=false source_units_mutually_authoritative=false "
        "parser_output_creates_ontology_truth=false candidate_only=true semantic_promotion=false",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
