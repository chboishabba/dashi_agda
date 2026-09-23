from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ERIC_PATH = ROOT / "interop_scripts" / "digital_esd_eric.py"

spec = importlib.util.spec_from_file_location("digital_esd_eric", ERIC_PATH)
assert spec and spec.loader
eric = importlib.util.module_from_spec(spec)
spec.loader.exec_module(eric)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def write_query(
    root: Path,
    qid: str,
    docs: list[dict],
    *,
    query: str = "fixture query",
) -> None:
    qdir = root / qid
    qdir.mkdir(parents=True, exist_ok=True)
    payload = {
        "response": {
            "numFound": len(docs),
            "start": 0,
            "docs": docs,
        }
    }
    raw = json.dumps(payload, sort_keys=True).encode("utf-8")
    page = qdir / "page-000000.json"
    page.write_bytes(raw)
    summary = {
        "query_id": qid,
        "canonical_unencoded_query": query,
        "numFound": len(docs),
        "fetched_docs": len(docs),
        "pagination_complete": True,
        "pages": [{
            "page_index": 0,
            "start": 0,
            "rows_requested": 200,
            "docs_returned": len(docs),
            "request_url": f"https://api.ies.ed.gov/eric/?fixture={qid}",
            "path": str(page),
            "sha256": sha256_bytes(raw),
        }],
    }
    (qdir / "summary.json").write_text(json.dumps(summary), encoding="utf-8")


def test_real_eric_records_dedup_across_queries_and_preserve_membership(
    tmp_path: Path,
) -> None:
    common = {
        "id": "EJ123456",
        "title": "Digital Learning for Sustainability",
        "author": ["Example, Alex"],
        "publicationdateyear": "2025",
        "description": "An empirical study of digital learning and sustainability.",
        "subject": ["Online Learning", "Sustainability"],
        "publicationtype": ["Journal Articles"],
        "peerreviewed": "T",
    }
    write_query(tmp_path, "Q1", [common])
    write_query(tmp_path, "Q2", [common])

    records, manifest = eric.parse_exports(tmp_path, ("Q1", "Q2"))
    assert manifest["raw_query_occurrence_count"] == 2
    assert manifest["unique_eric_record_count"] == 1

    row = records[0]
    assert row["source_identity_reference"] == "ERIC:EJ123456"
    assert row["query_memberships"] == ["Q1", "Q2"]
    assert row["abstract_present"] is True
    assert row["full_text_parsed"] is False
    assert row["full_text_retrieved"] is False
    assert row["creates_screening_decision"] is False
    assert row["creates_source_audit_admission"] is False


def test_conflicting_metadata_for_same_eric_id_fails_closed(
    tmp_path: Path,
) -> None:
    a = {
        "id": "EJ999999",
        "title": "Original title",
        "description": "Abstract A",
    }
    b = {
        "id": "EJ999999",
        "title": "Different title",
        "description": "Abstract A",
    }
    write_query(tmp_path, "Q1", [a])
    write_query(tmp_path, "Q2", [b])

    try:
        eric.parse_exports(tmp_path, ("Q1", "Q2"))
    except ValueError as exc:
        assert "conflicting normalized metadata" in str(exc)
    else:
        raise AssertionError("metadata conflict should fail closed")


def test_page_digest_drift_fails_closed(tmp_path: Path) -> None:
    doc = {"id": "EJ111111", "title": "Fixture", "description": "Abstract"}
    write_query(tmp_path, "Q1", [doc])
    page = tmp_path / "Q1" / "page-000000.json"
    page.write_text('{"response":{"numFound":0,"start":0,"docs":[]}}', encoding="utf-8")

    try:
        eric.parse_exports(tmp_path, ("Q1",))
    except ValueError as exc:
        assert "page digest mismatch" in str(exc)
    else:
        raise AssertionError("page digest drift should fail closed")
