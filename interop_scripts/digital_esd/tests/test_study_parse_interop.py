from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
PREPARE = ROOT / "interop_scripts/digital_esd/prepare_slr_source_units.py"
COMPILE = ROOT / "interop_scripts/digital_esd/compile_study_extraction_packets.py"


def write_jsonl(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as f:
        for row in rows:
            f.write(json.dumps(row, sort_keys=True) + "\n")


def read_jsonl(path: Path) -> list[dict]:
    with path.open(encoding="utf-8") as f:
        return [json.loads(line) for line in f if line.strip()]


def parser_record(unit_ref: str, revision_ref: str) -> dict:
    return {
        "schema": "slr-source-unit-pnf-record-v1",
        "source_unit_ref": unit_ref,
        "source_kind": "scholarly-full-text",
        "source_role": "screened-digital-esd-study",
        "language": "en",
        "revision_ref": revision_ref,
        "manifestation": {"source_text_sha256": revision_ref.removeprefix("fulltext-sha256:")},
        "parser_receipt": {
            "document_ref": "document:test",
            "parser_model": "fixture-parser",
            "spacy_version": "fixture",
        },
        "pnf_candidates": [
            {
                "claim_candidate_id": "pnf:test:1",
                "document_ref": "document:test",
                "sentence_index": 0,
                "source_span_start": 0,
                "source_span_end": 80,
                "sentence_text_sha256": "b" * 64,
                "dependency_rows": [
                    {"text": "students", "lemma": "student"},
                    {"text": "digital", "lemma": "digital"},
                    {"text": "sustainability", "lemma": "sustainability"},
                    {"text": "study", "lemma": "study"},
                    {"text": "outcomes", "lemma": "outcome"},
                ],
            }
        ],
        "candidate_only": True,
        "semantic_promotion": False,
    }


def test_retained_fulltext_compiles_to_19_coordinate_candidate_packet(tmp_path: Path) -> None:
    text_path = tmp_path / "paper.txt"
    text_path.write_text("fixture", encoding="utf-8")
    digest = hashlib.sha256(text_path.read_bytes()).hexdigest()
    fulltext = tmp_path / "fulltext.jsonl"
    write_jsonl(fulltext, [{
        "source_identity_reference": "ERIC:EJ1",
        "screening_decision_reference": "decision:1",
        "screening_decision": "probable",
        "text_path": str(text_path),
        "full_text_sha256": digest,
        "full_text_obtained": True,
        "same_object_identity_review_reference": "identity-review:1",
        "language": "en",
    }])
    source_units = tmp_path / "source-units.jsonl"
    subprocess.run(
        [sys.executable, str(PREPARE), "--fulltext-index", str(fulltext),
         "--output", str(source_units), "--purpose", "retained-study"],
        check=True,
    )
    unit = read_jsonl(source_units)[0]
    record_path = tmp_path / "record.json"
    record_path.write_text(
        json.dumps(parser_record(unit["source_unit_ref"], unit["revision_ref"])),
        encoding="utf-8",
    )
    manifest = tmp_path / "manifest.jsonl"
    write_jsonl(manifest, [{
        "source_unit_ref": unit["source_unit_ref"],
        "record_path": str(record_path),
        "source_text_sha256": digest,
    }])
    out = tmp_path / "packets"
    subprocess.run(
        [sys.executable, str(COMPILE), "--source-units", str(source_units),
         "--parser-manifest", str(manifest), "--output-dir", str(out)],
        check=True,
    )
    packets = read_jsonl(out / "study-extraction-candidate-packets.jsonl")
    assert len(packets) == 1
    assert packets[0]["extraction_schema_coordinate_count"] == 19
    assert all(c["coordinate_paid"] is False for c in packets[0]["extraction_coordinates"])
    assert packets[0]["source_audit_admission_created"] is False


def test_resolution_parse_cannot_leak_into_study_audit_packet(tmp_path: Path) -> None:
    unit = {
        "source_unit_ref": "digital-esd:ERIC:EJ2:" + "d" * 64,
        "source_kind": "scholarly-full-text",
        "source_role": "digital-esd-screening-resolution",
        "language": "en",
        "revision_ref": "fulltext-sha256:" + "d" * 64,
        "digital_esd_source_identity_reference": "ERIC:EJ2",
        "same_object_identity_review_reference": "identity-review:2",
        "screening_decision": "unresolved",
        "screening_decision_reference": "decision:2",
    }
    source_units = tmp_path / "source-units.jsonl"
    write_jsonl(source_units, [unit])
    record_path = tmp_path / "record.json"
    record_path.write_text(
        json.dumps(parser_record(unit["source_unit_ref"], unit["revision_ref"])),
        encoding="utf-8",
    )
    manifest = tmp_path / "manifest.jsonl"
    write_jsonl(manifest, [{
        "source_unit_ref": unit["source_unit_ref"],
        "record_path": str(record_path),
        "source_text_sha256": "d" * 64,
    }])
    out = tmp_path / "packets"
    subprocess.run(
        [sys.executable, str(COMPILE), "--source-units", str(source_units),
         "--parser-manifest", str(manifest), "--output-dir", str(out)],
        check=True,
    )
    assert read_jsonl(out / "study-extraction-candidate-packets.jsonl") == []
    resolution = read_jsonl(out / "screening-resolution-parse-packets.jsonl")
    assert len(resolution) == 1
    assert resolution[0]["creates_inclusion"] is False
    assert resolution[0]["creates_source_audit_admission"] is False
