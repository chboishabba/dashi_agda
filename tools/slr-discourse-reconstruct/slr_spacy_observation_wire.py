#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import struct
import sys
from typing import BinaryIO

MAGIC = b"SLRO"
VERSION = 1

NOMINAL_SUBJECT = 1
DIRECT_OBJECT = 2
PASSIVE_SUBJECT = 3
ADJECTIVAL_MODIFIER = 4
NOMINAL_MODIFIER = 5
CONJUNCTION = 6
NEGATION = 7
MODAL_AUXILIARY = 8
DETERMINER = 9
TEMPORAL_MODIFIER = 10
CLAUSAL_COMPLEMENT = 11
OPEN_CLAUSAL_COMPLEMENT = 12
ADVERBIAL_CLAUSE = 13
CLAUSAL_MODIFIER = 14
RELATIVE_CLAUSE = 15
UNRESOLVED_DEPENDENCY = 16

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


def dependency_shape(label: str) -> int:
    key = label.lower()
    if key in {"nsubj", "csubj"}:
        return NOMINAL_SUBJECT
    if key in {"obj", "dobj", "iobj", "pobj"}:
        return DIRECT_OBJECT
    if key in {"nsubjpass", "nsubj:pass", "csubjpass", "csubj:pass"}:
        return PASSIVE_SUBJECT
    if key == "amod":
        return ADJECTIVAL_MODIFIER
    if key in {"nmod", "obl"}:
        return NOMINAL_MODIFIER
    if key in {"conj", "cc"}:
        return CONJUNCTION
    if key == "neg":
        return NEGATION
    if key in {"aux", "auxpass", "aux:pass", "cop"}:
        return MODAL_AUXILIARY
    if key == "det":
        return DETERMINER
    if key in {"npadvmod", "tmod"}:
        return TEMPORAL_MODIFIER
    if key == "ccomp":
        return CLAUSAL_COMPLEMENT
    if key == "xcomp":
        return OPEN_CLAUSAL_COMPLEMENT
    if key == "advcl":
        return ADVERBIAL_CLAUSE
    if key == "acl":
        return CLAUSAL_MODIFIER
    if key in {"relcl", "acl:relcl"}:
        return RELATIVE_CLAUSE
    return UNRESOLVED_DEPENDENCY


def _write_text(out: BinaryIO, value: str) -> None:
    data = value.encode("utf-8")
    out.write(struct.pack("<I", len(data)))
    out.write(data)


def _write_header(out: BinaryIO, kind: int) -> None:
    out.write(MAGIC)
    out.write(struct.pack("<H", VERSION))
    out.write(bytes([kind]))


def write_manifestation(
    out: BinaryIO,
    *,
    document_ref: str,
    qid: str,
    language: str,
    revision_ref: str,
    source_sha256: bytes,
) -> None:
    if len(source_sha256) != 32:
        raise ValueError("source_sha256 must be exactly 32 bytes")
    _write_header(out, 1)
    _write_text(out, document_ref)
    _write_text(out, qid)
    _write_text(out, language)
    _write_text(out, revision_ref)
    out.write(source_sha256)


def write_token(
    out: BinaryIO,
    *,
    document_ref: str,
    sentence_id: int,
    local_ordinal: int,
    start_char: int,
    end_char: int,
    head_ordinal: int,
    dependency_shape: int,
    orth: str,
    lemma: str,
    head_orth: str,
    head_lemma: str,
) -> None:
    _write_header(out, 2)
    _write_text(out, document_ref)
    out.write(struct.pack("<Q", sentence_id))
    out.write(struct.pack("<I", local_ordinal))
    out.write(struct.pack("<I", start_char))
    out.write(struct.pack("<I", end_char))
    out.write(struct.pack("<I", head_ordinal))
    out.write(bytes([dependency_shape]))
    _write_text(out, orth)
    _write_text(out, lemma)
    _write_text(out, head_orth)
    _write_text(out, head_lemma)


def emit_spacy_observations(
    text: str,
    *,
    document_ref: str,
    qid: str,
    language: str,
    revision_ref: str,
    out: BinaryIO,
    model_name: str | None = None,
) -> tuple[int, int]:
    import spacy  # type: ignore

    model = model_name or MODEL_BY_LANG.get(language, f"{language}_core_news_sm")
    nlp = spacy.load(model)
    if "parser" not in nlp.pipe_names:
        raise RuntimeError(f"trained dependency parser required: {language}:{model}")

    write_manifestation(
        out,
        document_ref=document_ref,
        qid=qid,
        language=language,
        revision_ref=revision_ref,
        source_sha256=hashlib.sha256(text.encode("utf-8")).digest(),
    )

    doc = nlp(text)
    sentence_count = 0
    token_count = 0
    for sentence_id, sent in enumerate(doc.sents):
        sentence_count += 1
        for local_ordinal, tok in enumerate(sent):
            head_ordinal = int(tok.head.i - sent.start)
            write_token(
                out,
                document_ref=document_ref,
                sentence_id=sentence_id,
                local_ordinal=local_ordinal,
                start_char=int(tok.idx),
                end_char=int(tok.idx + len(tok.text)),
                head_ordinal=head_ordinal,
                dependency_shape=dependency_shape(tok.dep_),
                orth=tok.text,
                lemma=tok.lemma_,
                head_orth=tok.head.text,
                head_lemma=tok.head.lemma_,
            )
            token_count += 1
    return sentence_count, token_count


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--text", type=Path, required=True)
    p.add_argument("--document-ref", required=True)
    p.add_argument("--qid", required=True)
    p.add_argument("--language", required=True)
    p.add_argument("--revision-ref", required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--model")
    return p.parse_args()


def main() -> int:
    args = parse_args()
    text = args.text.read_text(encoding="utf-8")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("wb") as out:
        sentences, tokens = emit_spacy_observations(
            text,
            document_ref=args.document_ref,
            qid=args.qid,
            language=args.language,
            revision_ref=args.revision_ref,
            out=out,
            model_name=args.model,
        )
    print(
        "SLR_SPACY_OBSERVATION_BINARY_RECEIPT "
        f"sentences={sentences} tokens={tokens} binary_wire=true json_transport=false regex_parser=false "
        "parser_output_creates_ontology_truth=false candidate_only=true semantic_promotion=false",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
