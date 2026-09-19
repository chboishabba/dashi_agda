#!/usr/bin/env python3
"""Create candidate-only Digital-ESD screening assessments and study-family hypotheses.

This tool never edits or replaces the authoritative screening ledger.

Inputs:
  --metadata  exact deduplicated metadata JSON
  --ledger    screening-decisions.jsonl produced by
              prepare_digital_esd_screening_ledger.py

Outputs:
  candidate-assessments.jsonl
  study-family-hypotheses.jsonl
  study-family-fibres.jsonl
  assessment-manifest.json

Authority boundary:
  candidate assessment != screening decision
  similarity != duplicate decision
  study-family hypothesis != same empirical study
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import re
from collections import defaultdict
from difflib import SequenceMatcher
from pathlib import Path
from typing import Any


DIGITAL_TERMS = {
    "digital education", "digital learning", "educational technology", "edtech",
    "online learning", "blended learning", "learning platform", "artificial intelligence",
    "generative ai", "digital technology", "digital technologies",
}
SUSTAINABILITY_TERMS = {
    "education for sustainable development", "sustainability education",
    "sustainable development", "environmental education", "sustainability",
    "environmental sustainability", "e-waste", "circularity", "repairability",
    "life cycle", "lifecycle", "carbon", "energy use", "emissions",
}
EMPIRICAL_TERMS = {
    "study", "participants", "sample", "survey", "interview", "experiment",
    "randomized", "randomised", "case study", "longitudinal", "evaluation",
    "mixed methods", "qualitative", "quantitative", "students", "teachers",
}

WORD_RE = re.compile(r"[a-z0-9]+")
DOI_RE = re.compile(r"10\.\d{4,9}/[-._;()/:a-z0-9]+", re.I)


def canonical_bytes(value: Any) -> bytes:
    return (json.dumps(value, sort_keys=True, ensure_ascii=False, separators=(",", ":")) + "\n").encode()


def sha256_json(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    out = []
    with path.open("r", encoding="utf-8") as handle:
        for n, line in enumerate(handle, 1):
            if not line.strip():
                continue
            row = json.loads(line)
            if not isinstance(row, dict):
                raise ValueError(f"{path}:{n}: expected object")
            out.append(row)
    return out


def load_metadata(path: Path) -> list[dict[str, Any]]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if isinstance(payload, list):
        rows = payload
    elif isinstance(payload, dict):
        rows = next((payload[k] for k in ("records", "items", "docs", "results") if isinstance(payload.get(k), list)), None)
        if rows is None:
            raise ValueError("metadata JSON has no records/items/docs/results array")
    else:
        raise ValueError("metadata input must be array or object containing an array")
    return [r for r in rows if isinstance(r, dict)]


def first_text(row: dict[str, Any], *keys: str) -> str:
    for key in keys:
        value = row.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip()
        if isinstance(value, list) and value:
            joined = "; ".join(str(x) for x in value if x is not None)
            if joined.strip():
                return joined.strip()
    return ""


def normalize_space(value: str) -> str:
    return " ".join(value.split()).strip()


def source_identity(row: dict[str, Any]) -> str:
    eric_id = first_text(row, "ID", "id", "ERICNumber", "eric_id", "ericId")
    if eric_id:
        return "ERIC:" + normalize_space(eric_id)
    doi = first_text(row, "DOI", "doi")
    if doi:
        return "DOI:" + normalize_space(doi).lower()
    title = first_text(row, "Title", "title")
    year = first_text(row, "PublicationDate", "publication_date", "Year", "year")
    author = first_text(row, "Author", "Authors", "author", "authors")
    return "METADATA:" + sha256_json({"title": title, "year": year, "author": author, "metadata_sha256": sha256_json(row)})


def normalized_title(row: dict[str, Any]) -> str:
    title = first_text(row, "Title", "title")
    return " ".join(WORD_RE.findall(title.lower()))


def first_author(row: dict[str, Any]) -> str:
    raw = first_text(row, "Author", "Authors", "author", "authors")
    if not raw:
        return ""
    head = re.split(r";|\band\b|\|", raw, maxsplit=1, flags=re.I)[0]
    return " ".join(WORD_RE.findall(head.lower()))


def year_value(row: dict[str, Any]) -> str:
    text = first_text(row, "PublicationDate", "publication_date", "Year", "year")
    m = re.search(r"(19|20)\d{2}", text)
    return m.group(0) if m else ""


def doi_value(row: dict[str, Any]) -> str:
    explicit = first_text(row, "DOI", "doi")
    if explicit:
        m = DOI_RE.search(explicit)
        return m.group(0).lower().rstrip(".,;)") if m else explicit.lower()
    haystack = " ".join(str(v) for v in row.values() if isinstance(v, str))
    m = DOI_RE.search(haystack)
    return m.group(0).lower().rstrip(".,;)") if m else ""


def phrase_hits(text: str, terms: set[str]) -> list[str]:
    lower = text.lower()
    return sorted(term for term in terms if term in lower)


def candidate_assessment(ledger: dict[str, Any], metadata: dict[str, Any]) -> dict[str, Any]:
    snap = ledger.get("title_abstract_snapshot") or {}
    title = str(snap.get("title") or first_text(metadata, "Title", "title"))
    abstract = str(snap.get("abstract") or first_text(metadata, "Description", "description", "Abstract", "abstract"))
    text = normalize_space(title + " " + abstract)

    digital = phrase_hits(text, DIGITAL_TERMS)
    sustainability = phrase_hits(text, SUSTAINABILITY_TERMS)
    empirical = phrase_hits(text, EMPIRICAL_TERMS)

    reasons: list[str] = []
    if not abstract.strip():
        candidate = "unresolved"
        reasons.append("inaccessibleAbstract")
        confidence = "insufficient-text"
        margin = "0"
    elif digital and sustainability:
        candidate = "probable"
        reasons.extend(["potentiallyRelevant", "requiresFullText"])
        confidence = "high-candidate-relevance" if empirical else "moderate-candidate-relevance"
        margin = str(len(digital) + len(sustainability) + len(empirical))
    elif not digital and not sustainability and len(text) >= 200:
        candidate = "exclude"
        reasons.extend(["educationContextMismatch", "sustainabilityQuestionMismatch"])
        confidence = "high-candidate-mismatch"
        margin = str(min(20, len(text) // 100))
    else:
        candidate = "unresolved"
        reasons.append("insufficientTitleAbstractEvidence")
        confidence = "boundary"
        margin = str(abs(len(digital) - len(sustainability)))

    feature_payload = {
        "digital_hits": digital,
        "sustainability_hits": sustainability,
        "empirical_hits": empirical,
        "title_length": len(title),
        "abstract_length": len(abstract),
        "publication_type": snap.get("publication_type"),
        "peer_reviewed": snap.get("peer_reviewed"),
    }
    assessment_basis = {
        "source_identity_reference": ledger["source_identity_reference"],
        "metadata_revision_reference": ledger["metadata_revision_reference"],
        "candidate_decision": candidate,
        "reason_codes": reasons,
        "features": feature_payload,
        "rubric_version": ledger["screening_rubric_version"],
    }
    ref = "screening-candidate-assessment:" + sha256_json(assessment_basis)
    return {
        "schema": "digital-esd-screening-candidate-assessment-v1",
        "assessment_reference": ref,
        "source_identity_reference": ledger["source_identity_reference"],
        "metadata_revision_reference": ledger["metadata_revision_reference"],
        "title_abstract_snapshot_reference": ledger["title_abstract_snapshot_reference"],
        "rubric_version": ledger["screening_rubric_version"],
        "candidate_decision": candidate,
        "candidate_reason_codes": reasons,
        "feature_evidence": feature_payload,
        "feature_evidence_reference": "feature-evidence:" + sha256_json(feature_payload),
        "model_or_process_reference": "deterministic-rubric-signals:v1",
        "confidence_reference": confidence,
        "margin_reference": margin,
        "candidate_only": True,
        "explicitly_reviewed": False,
        "creates_screening_decision": False,
        "creates_exclusion": False,
        "creates_source_truth": False,
    }


class DSU:
    def __init__(self) -> None:
        self.parent: dict[str, str] = {}

    def find(self, x: str) -> str:
        self.parent.setdefault(x, x)
        if self.parent[x] != x:
            self.parent[x] = self.find(self.parent[x])
        return self.parent[x]

    def union(self, a: str, b: str) -> None:
        ra, rb = self.find(a), self.find(b)
        if ra != rb:
            self.parent[rb] = ra


def hypothesis(a_ref: str, b_ref: str, relation: str, evidence: dict[str, Any]) -> dict[str, Any]:
    payload = {"left": a_ref, "right": b_ref, "relation": relation, "evidence": evidence}
    return {
        "schema": "digital-esd-study-family-hypothesis-v1",
        "hypothesis_reference": "study-family-hypothesis:" + sha256_json(payload),
        "left_source_identity_reference": a_ref,
        "right_source_identity_reference": b_ref,
        "proposed_relation": relation,
        "evidence": evidence,
        "candidate_only": True,
        "creates_duplicate_decision": False,
        "creates_same_empirical_study": False,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--metadata", type=Path, required=True)
    ap.add_argument("--ledger", type=Path, required=True)
    ap.add_argument("--out-dir", type=Path, default=Path("artifacts/digital-esd/screening/adaptive"))
    ap.add_argument("--fuzzy-title-threshold", type=float, default=0.94)
    ap.add_argument("--max-fuzzy-block", type=int, default=40)
    args = ap.parse_args()

    metadata_rows = load_metadata(args.metadata)
    metadata_by_ref = {source_identity(row): row for row in metadata_rows}
    ledger_rows = read_jsonl(args.ledger)
    if len(metadata_by_ref) != len(metadata_rows):
        raise RuntimeError("metadata input contains duplicate stable source identities")

    args.out_dir.mkdir(parents=True, exist_ok=True)
    assessments_path = args.out_dir / "candidate-assessments.jsonl"
    hypotheses_path = args.out_dir / "study-family-hypotheses.jsonl"
    fibres_path = args.out_dir / "study-family-fibres.jsonl"

    assessments = []
    for ledger in ledger_rows:
        ref = ledger["source_identity_reference"]
        if ref not in metadata_by_ref:
            raise RuntimeError(f"ledger source absent from exact metadata set: {ref}")
        assessments.append(candidate_assessment(ledger, metadata_by_ref[ref]))

    with assessments_path.open("w", encoding="utf-8") as fh:
        for row in assessments:
            fh.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")

    doi_index: dict[str, list[str]] = defaultdict(list)
    title_index: dict[str, list[str]] = defaultdict(list)
    fuzzy_blocks: dict[tuple[str, str], list[str]] = defaultdict(list)
    for ref, row in metadata_by_ref.items():
        doi = doi_value(row)
        title = normalized_title(row)
        author = first_author(row)
        year = year_value(row)
        if doi:
            doi_index[doi].append(ref)
        if title:
            title_index[title].append(ref)
        if author and year and title:
            fuzzy_blocks[(author, year)].append(ref)

    edges: dict[tuple[str, str, str], dict[str, Any]] = {}

    def add_edge(left: str, right: str, relation: str, evidence: dict[str, Any]) -> None:
        a, b = sorted((left, right))
        key = (a, b, relation)
        edges.setdefault(key, hypothesis(a, b, relation, evidence))

    for doi, refs in doi_index.items():
        for a, b in itertools.combinations(sorted(set(refs)), 2):
            add_edge(a, b, "publicationDuplicate", {"doi": doi, "basis": "exact-doi"})

    for title, refs in title_index.items():
        for a, b in itertools.combinations(sorted(set(refs)), 2):
            add_edge(a, b, "publicationDuplicate", {"normalized_title": title, "basis": "exact-normalized-title"})

    for (author, year), refs in fuzzy_blocks.items():
        refs = sorted(set(refs))
        if len(refs) > args.max_fuzzy_block:
            continue
        for a, b in itertools.combinations(refs, 2):
            ta = normalized_title(metadata_by_ref[a])
            tb = normalized_title(metadata_by_ref[b])
            ratio = SequenceMatcher(None, ta, tb).ratio()
            if ratio >= args.fuzzy_title_threshold and ta != tb:
                add_edge(
                    a, b, "reportFamilyDuplicate",
                    {"first_author": author, "year": year, "title_similarity": round(ratio, 6), "basis": "blocked-fuzzy-title"},
                )

    hypotheses = list(edges.values())
    with hypotheses_path.open("w", encoding="utf-8") as fh:
        for row in hypotheses:
            fh.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")

    dsu = DSU()
    hyp_refs_by_root_input: dict[str, list[str]] = defaultdict(list)
    for row in hypotheses:
        a = row["left_source_identity_reference"]
        b = row["right_source_identity_reference"]
        dsu.union(a, b)
    groups: dict[str, list[str]] = defaultdict(list)
    for ref in metadata_by_ref:
        root = dsu.find(ref)
        if root != ref or any(ref in (h["left_source_identity_reference"], h["right_source_identity_reference"]) for h in hypotheses):
            groups[root].append(ref)
    for row in hypotheses:
        root = dsu.find(row["left_source_identity_reference"])
        hyp_refs_by_root_input[root].append(row["hypothesis_reference"])

    fibres = []
    for root, members in groups.items():
        if len(members) < 2:
            continue
        payload = {"members": sorted(members), "hypotheses": sorted(hyp_refs_by_root_input[root])}
        fibres.append({
            "schema": "digital-esd-study-family-candidate-fibre-v1",
            "fibre_reference": "study-family-fibre:" + sha256_json(payload),
            "representative_source_reference": sorted(members)[0],
            "member_source_references": sorted(members),
            "hypothesis_references": sorted(hyp_refs_by_root_input[root]),
            "reviewed_as_same_empirical_study": False,
        })

    with fibres_path.open("w", encoding="utf-8") as fh:
        for row in fibres:
            fh.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")

    manifest = {
        "schema": "digital-esd-adaptive-screening-assessment-manifest-v1",
        "metadata_reference": str(args.metadata),
        "ledger_reference": str(args.ledger),
        "assessment_count": len(assessments),
        "hypothesis_count": len(hypotheses),
        "candidate_fibre_count": len(fibres),
        "candidate_assessment_creates_screening_decision": False,
        "candidate_assessment_creates_exclusion": False,
        "study_family_hypothesis_creates_same_empirical_study": False,
    }
    (args.out_dir / "assessment-manifest.json").write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(manifest, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
