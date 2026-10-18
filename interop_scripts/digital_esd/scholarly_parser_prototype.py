#!/usr/bin/env python3
"""Prototype generic scholarly-document parser for Digital-ESD fixtures.

This is intentionally application-side prototype machinery.

It implements the output contract consumed by:
  interop_scripts/digital_esd/scholarly_fulltext.py

and formalised by:
  DASHI.Interop.DigitalESD.ScholarlyFullTextCrossPollinationExact

Supported input formats:
  .txt / .md       exact text-range anchors
  .html / .htm     structured block coordinates
  .docx            structured paragraph/table coordinates
  .pdf             structured page/block coordinates via pypdf or PyMuPDF

The parser emits:
  * addressable document nodes;
  * generic scholarly-study facet candidates;
  * candidate EvidenceObservation-shaped records.

It does NOT review observations, decide Digital-ESD relevance, create study
truth, or construct SourceAuditAdmission.

This file is a proving ground for what may later become generic SLR scholarly
document infrastructure. Do not treat its heuristics as a production semantic
ABI.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re
import sys
import zipfile
from typing import Any, Iterable
import xml.etree.ElementTree as ET


PARSER_VERSION = "digital-esd-scholarly-parser-prototype-v1"

BLOCK_TAGS = {
    "article", "aside", "blockquote", "caption", "dd", "div", "dl", "dt",
    "figcaption", "footer", "h1", "h2", "h3", "h4", "h5", "h6", "header",
    "li", "main", "p", "pre", "section", "td", "th", "tr",
}

HEADING_TAGS = {"h1", "h2", "h3", "h4", "h5", "h6"}

SENTENCE_RE = re.compile(r"(?<=[.!?])\s+(?=[A-Z0-9])")

FACET_PATTERNS: dict[str, tuple[re.Pattern[str], ...]] = {
    "population": (
        re.compile(r"\b(population|participants?|students?|teachers?|learners?|children|adolescents?|adults?|respondents?)\b", re.I),
    ),
    "sample": (
        re.compile(r"\bn\s*=\s*\d+\b", re.I),
        re.compile(r"\b\d+\s+(participants?|students?|teachers?|respondents?|cases?)\b", re.I),
        re.compile(r"\b(sample|sampled|sampling)\b", re.I),
    ),
    "intervention": (
        re.compile(r"\b(intervention|programme|program|course|training|simulation|platform|tool|curriculum|module|workshop)\b", re.I),
    ),
    "comparator": (
        re.compile(r"\b(control group|comparison group|comparator|usual care|business as usual|baseline group)\b", re.I),
    ),
    "outcome": (
        re.compile(r"\b(outcome|result|score|achievement|performance|knowledge|attitude|behavio(?:u)?r|competenc|engagement|retention|wellbeing|well-being)\w*\b", re.I),
    ),
    "study_design": (
        re.compile(r"\b(randomi[sz]ed|randomi[sz]ation|RCT|quasi-experimental|case study|cross-sectional|longitudinal|cohort|experimental design)\b", re.I),
    ),
    "setting": (
        re.compile(r"\b(university|universities|school|schools|college|higher education|secondary education|primary education|online|distance education|classroom)\b", re.I),
    ),
    "time_period": (
        re.compile(r"\b\d+\s*(day|week|month|year)s?\b", re.I),
        re.compile(r"\b(follow-up|follow up|baseline|pre-test|pretest|post-test|posttest|longitudinal)\b", re.I),
    ),
    "method": (
        re.compile(r"\b(survey|questionnaire|interview|focus group|mixed methods?|qualitative|quantitative|regression|ANOVA|thematic analysis|content analysis|ethnograph)\w*\b", re.I),
    ),
    "limitation": (
        re.compile(r"\b(limitations?|self-selection|selection bias|attrition|dropout|small sample|confound|missing data|generalizability|generalisability)\w*\b", re.I),
    ),
    "funding": (
        re.compile(r"\b(funded by|funding|grant|financial support|sponsor(?:ed|ship)?)\b", re.I),
    ),
    "institution": (
        re.compile(r"\b(university|institute|institution|school|college|department|faculty)\b", re.I),
    ),
    "participant_group": (
        re.compile(r"\b(disab(?:led|ility)|neurodiverg|indigenous|first nations|migrant|refugee|low-income|socioeconomic|gender|transgender|racial|ethnic|caregiver|carer|parent)\w*\b", re.I),
    ),
    "measurement": (
        re.compile(r"\b(scale|questionnaire|instrument|measure|index|inventory|test|assessment|rubric)\b", re.I),
    ),
}


@dataclass(frozen=True)
class Block:
    kind: str
    coordinate: str
    text: str
    start: int | None = None
    end: int | None = None


def canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
        + "\n"
    ).encode("utf-8")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line_no, line in enumerate(handle, start=1):
            if not line.strip():
                continue
            row = json.loads(line)
            if not isinstance(row, dict):
                raise ValueError(f"{path}:{line_no}: expected JSON object")
            rows.append(row)
    return rows


class BlockHTMLParser(HTMLParser):
    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self._stack: list[str] = []
        self._buffer: list[str] = []
        self.blocks: list[tuple[str, str]] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        tag = tag.lower()
        self._stack.append(tag)
        if tag in BLOCK_TAGS and self._buffer:
            self._flush("paragraph")

    def handle_endtag(self, tag: str) -> None:
        tag = tag.lower()
        if tag in BLOCK_TAGS:
            kind = "heading" if tag in HEADING_TAGS else (
                "table_cell" if tag in {"td", "th"} else "paragraph"
            )
            self._flush(kind)
        if self._stack:
            # HTML can be malformed; remove the nearest matching tag if present.
            try:
                idx = len(self._stack) - 1 - self._stack[::-1].index(tag)
                del self._stack[idx]
            except ValueError:
                pass

    def handle_data(self, data: str) -> None:
        if any(tag in {"script", "style", "noscript"} for tag in self._stack):
            return
        text = " ".join(data.split())
        if text:
            self._buffer.append(text)

    def close(self) -> None:
        super().close()
        self._flush("paragraph")

    def _flush(self, kind: str) -> None:
        text = " ".join(self._buffer).strip()
        self._buffer.clear()
        if text:
            self.blocks.append((kind, text))


def parse_plain_text(path: Path) -> tuple[str, list[Block]]:
    text = path.read_text(encoding="utf-8", errors="replace")
    blocks: list[Block] = []
    for idx, match in enumerate(re.finditer(r"\S(?:.*?\S)?(?=\n\s*\n|\Z)", text, re.S)):
        raw = match.group(0)
        normalized = " ".join(raw.split())
        if not normalized:
            continue
        stripped = raw.strip()
        start = match.start() + raw.index(stripped)
        end = start + len(stripped)
        first_line = stripped.splitlines()[0].strip()
        kind = "heading" if (
            len(stripped.splitlines()) == 1
            and len(first_line) <= 160
            and (
                first_line.isupper()
                or re.match(r"^\d+(?:\.\d+)*\s+\S", first_line)
                or first_line.lower() in {
                    "abstract", "introduction", "methods", "method", "results",
                    "discussion", "conclusion", "conclusions", "limitations",
                    "references", "acknowledgements", "funding",
                }
            )
        ) else "paragraph"
        blocks.append(Block(kind, f"text:block:{idx}", normalized, start, end))
    return text, blocks


def parse_html(path: Path) -> tuple[str, list[Block]]:
    parser = BlockHTMLParser()
    parser.feed(path.read_text(encoding="utf-8", errors="replace"))
    parser.close()
    blocks = [
        Block(kind, f"html:block:{i}", text)
        for i, (kind, text) in enumerate(parser.blocks)
    ]
    canonical = "\n\n".join(block.text for block in blocks)
    return canonical, blocks


def _docx_text(element: ET.Element) -> str:
    texts = []
    for node in element.iter():
        if node.tag.endswith("}t") and node.text:
            texts.append(node.text)
    return " ".join(" ".join(texts).split())


def parse_docx(path: Path) -> tuple[str, list[Block]]:
    blocks: list[Block] = []
    with zipfile.ZipFile(path) as archive:
        xml = archive.read("word/document.xml")
    root = ET.fromstring(xml)
    body = next((x for x in root.iter() if x.tag.endswith("}body")), root)
    paragraph_index = 0
    table_index = 0
    for child in list(body):
        if child.tag.endswith("}p"):
            text = _docx_text(child)
            if text:
                blocks.append(
                    Block("paragraph", f"docx:paragraph:{paragraph_index}", text)
                )
                paragraph_index += 1
        elif child.tag.endswith("}tbl"):
            row_index = 0
            for row in [x for x in list(child) if x.tag.endswith("}tr")]:
                cell_index = 0
                for cell in [x for x in list(row) if x.tag.endswith("}tc")]:
                    text = _docx_text(cell)
                    if text:
                        blocks.append(
                            Block(
                                "table_cell",
                                f"docx:table:{table_index}:row:{row_index}:cell:{cell_index}",
                                text,
                            )
                        )
                    cell_index += 1
                row_index += 1
            table_index += 1
    canonical = "\n\n".join(block.text for block in blocks)
    return canonical, blocks


def parse_pdf(path: Path) -> tuple[str, list[Block]]:
    # Prefer pypdf because it is pure Python and common in scholarly workflows.
    try:
        from pypdf import PdfReader  # type: ignore

        reader = PdfReader(str(path))
        blocks: list[Block] = []
        all_text: list[str] = []
        for page_index, page in enumerate(reader.pages):
            text = page.extract_text() or ""
            paragraphs = [
                " ".join(p.split())
                for p in re.split(r"\n\s*\n|(?<!\n)\n(?=[A-Z])", text)
                if " ".join(p.split())
            ]
            for block_index, paragraph in enumerate(paragraphs):
                blocks.append(
                    Block(
                        "paragraph",
                        f"pdf:page:{page_index + 1}:block:{block_index}",
                        paragraph,
                    )
                )
                all_text.append(paragraph)
        return "\n\n".join(all_text), blocks
    except ImportError:
        pass

    try:
        import fitz  # type: ignore

        document = fitz.open(str(path))
        blocks = []
        all_text = []
        for page_index, page in enumerate(document):
            raw_blocks = page.get_text("blocks")
            for block_index, block in enumerate(raw_blocks):
                text = " ".join(str(block[4]).split())
                if not text:
                    continue
                blocks.append(
                    Block(
                        "paragraph",
                        f"pdf:page:{page_index + 1}:block:{block_index}",
                        text,
                    )
                )
                all_text.append(text)
        return "\n\n".join(all_text), blocks
    except ImportError as exc:
        raise RuntimeError(
            "PDF parsing requires either pypdf or PyMuPDF (fitz); "
            "install one locally or configure a different parser capability"
        ) from exc


def parse_artifact(path: Path) -> tuple[str, list[Block], str]:
    suffix = path.suffix.lower()
    if suffix in {".txt", ".md", ".text"}:
        text, blocks = parse_plain_text(path)
        return text, blocks, "plain_text"
    if suffix in {".html", ".htm"}:
        text, blocks = parse_html(path)
        return text, blocks, "html"
    if suffix == ".docx":
        text, blocks = parse_docx(path)
        return text, blocks, "docx"
    if suffix == ".pdf":
        text, blocks = parse_pdf(path)
        return text, blocks, "pdf"
    raise RuntimeError(
        f"unsupported scholarly artifact suffix {suffix!r}; "
        "supported: txt/md/html/docx/pdf"
    )


def split_sentences(text: str) -> Iterable[str]:
    for sentence in SENTENCE_RE.split(" ".join(text.split())):
        sentence = sentence.strip()
        if len(sentence) >= 20:
            yield sentence


def make_span(block: Block, revision_ref: str) -> dict[str, Any]:
    span_ref = "span:" + hashlib.sha256(
        f"{revision_ref}\0{block.coordinate}".encode("utf-8")
    ).hexdigest()
    if block.start is not None and block.end is not None:
        return {
            "span_ref": span_ref,
            "source_revision_ref": revision_ref,
            "kind": "text_range",
            "start": block.start,
            "end": block.end,
        }
    return {
        "span_ref": span_ref,
        "source_revision_ref": revision_ref,
        "kind": "structured_coordinate",
        "coordinate": block.coordinate,
    }


def make_node(
    block: Block,
    revision_ref: str,
    parser_receipt_ref: str,
    index: int,
) -> dict[str, Any]:
    return {
        "node_reference": f"document-node:{index}:"
        + hashlib.sha256(
            f"{revision_ref}\0{block.coordinate}\0{block.text}".encode("utf-8")
        ).hexdigest(),
        "node_kind": block.kind if block.kind in {
            "heading", "paragraph", "table_cell"
        } else "other",
        "span": make_span(block, revision_ref),
        "parser_or_layout_receipt_reference": parser_receipt_ref,
        "text": block.text,
        "candidate_only": True,
        "creates_claim_truth": False,
        "creates_source_audit_admission": False,
    }


def facet_candidates(
    node: dict[str, Any],
    revision_ref: str,
    parser_receipt_ref: str,
) -> list[dict[str, Any]]:
    output: list[dict[str, Any]] = []
    text = str(node.get("text") or "")
    for sentence_index, sentence in enumerate(split_sentences(text)):
        for facet_kind, patterns in FACET_PATTERNS.items():
            if not any(pattern.search(sentence) for pattern in patterns):
                continue
            value_digest = hashlib.sha256(sentence.encode("utf-8")).hexdigest()
            facet_basis = (
                f"{revision_ref}\0{node['node_reference']}\0"
                f"{facet_kind}\0{sentence_index}\0{value_digest}"
            )
            digest = hashlib.sha256(facet_basis.encode("utf-8")).hexdigest()
            observation_ref = "observation:" + digest
            output.append({
                "facet_reference": "study-facet:" + digest,
                "facet_kind": facet_kind,
                "node_reference": node["node_reference"],
                "observation": {
                    "observation_ref": observation_ref,
                    "source_revision_ref": revision_ref,
                    "span_ref": node["span"]["span_ref"],
                    "predicate_ref": f"scholarly-study:{facet_kind}",
                    "value_ref": "text-sha256:" + value_digest,
                    "candidate_only": True,
                    "creates_semantic_authority": False,
                    "applicability_promoted": False,
                    "claim_truth_promoted": False,
                },
                "candidate_text": sentence,
                "parser_or_model_receipt_reference": parser_receipt_ref,
                "ontology_candidate_reference": f"scholarly-study-facet:{facet_kind}",
                "candidate_only": True,
                "creates_study_truth": False,
                "creates_screening_decision": False,
                "creates_source_audit_admission": False,
            })
    return output


def parse_request(row: dict[str, Any], line_no: int) -> dict[str, Any]:
    source_ref = str(row.get("source_identity_reference") or "").strip()
    revision_ref = str(row.get("source_revision_ref") or "").strip()
    digest_ref = str(row.get("content_digest_ref") or "").strip().lower()
    artifact_ref = str(row.get("artifact_reference") or "").strip()

    if not all((source_ref, revision_ref, digest_ref, artifact_ref)):
        raise ValueError(f"request row {line_no}: incomplete artifact identity")
    if not digest_ref.startswith("sha256:"):
        raise ValueError(f"request row {line_no}: digest must use sha256: prefix")

    path = Path(artifact_ref)
    if not path.exists():
        raise FileNotFoundError(f"request row {line_no}: artifact not found: {path}")
    observed_digest = "sha256:" + sha256_file(path)
    if observed_digest != digest_ref:
        raise ValueError(
            f"request row {line_no}: digest drift expected={digest_ref} "
            f"observed={observed_digest}"
        )

    canonical_text, blocks, media_kind = parse_artifact(path)
    canonical_text_digest = "sha256:" + sha256_bytes(canonical_text.encode("utf-8"))
    parser_receipt_basis = {
        "parser_version": PARSER_VERSION,
        "source_identity_reference": source_ref,
        "source_revision_ref": revision_ref,
        "content_digest_ref": digest_ref,
        "canonical_text_digest": canonical_text_digest,
        "media_kind": media_kind,
        "block_count": len(blocks),
    }
    parser_receipt_ref = "parser-receipt:" + sha256_bytes(
        canonical_json_bytes(parser_receipt_basis)
    )

    nodes = [
        make_node(block, revision_ref, parser_receipt_ref, index)
        for index, block in enumerate(blocks)
    ]
    facets = [
        facet
        for node in nodes
        for facet in facet_candidates(node, revision_ref, parser_receipt_ref)
    ]

    return {
        "schema": "digital-esd-scholarly-parser-bundle-v1",
        "source_identity_reference": source_ref,
        "source_revision_ref": revision_ref,
        "content_digest_ref": digest_ref,
        "artifact_reference": artifact_ref,
        "media_kind": media_kind,
        "canonical_text_digest_ref": canonical_text_digest,
        "parser_or_layout_receipt_reference": parser_receipt_ref,
        "document_nodes": nodes,
        "study_facets": facets,
        "candidate_only": True,
        "reviewed": False,
        "creates_semantic_authority": False,
        "applicability_promoted": False,
        "claim_truth_promoted": False,
        "creates_source_audit_admission": False,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", required=True, type=Path)
    ap.add_argument("--output", required=True, type=Path)
    args = ap.parse_args()

    requests = read_jsonl(args.input)
    bundles = [
        parse_request(row, line_no)
        for line_no, row in enumerate(requests, start=1)
    ]

    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", encoding="utf-8") as handle:
        for bundle in bundles:
            handle.write(json.dumps(bundle, ensure_ascii=False, sort_keys=True) + "\n")

    manifest = {
        "schema": "digital-esd-scholarly-parser-prototype-manifest-v1",
        "parser_version": PARSER_VERSION,
        "input_reference": str(args.input),
        "input_sha256": sha256_file(args.input),
        "output_reference": str(args.output),
        "output_sha256": sha256_file(args.output),
        "bundle_count": len(bundles),
        "document_node_count": sum(len(x["document_nodes"]) for x in bundles),
        "study_facet_count": sum(len(x["study_facets"]) for x in bundles),
        "prototype_is_production_semantic_abi": False,
        "candidate_only": True,
        "creates_review_payment": False,
        "creates_source_truth": False,
        "creates_source_audit_admission": False,
    }
    args.output.with_suffix(".manifest.json").write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(manifest, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
