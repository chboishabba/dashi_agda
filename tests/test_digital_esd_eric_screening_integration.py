from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


eric = load_module(
    "digital_esd_eric",
    ROOT / "interop_scripts" / "digital_esd_eric.py",
)
ledger = load_module(
    "prepare_digital_esd_screening_ledger",
    ROOT / "scripts" / "prepare_digital_esd_screening_ledger.py",
)


def write_query(root: Path, qid: str, docs: list[dict]) -> None:
    qdir = root / qid
    qdir.mkdir(parents=True, exist_ok=True)
    payload = {"response": {"numFound": len(docs), "start": 0, "docs": docs}}
    raw = json.dumps(payload, sort_keys=True).encode("utf-8")
    page = qdir / "page-000000.json"
    page.write_bytes(raw)
    (qdir / "summary.json").write_text(
        json.dumps(
            {
                "query_id": qid,
                "canonical_unencoded_query": "fixture",
                "numFound": len(docs),
                "fetched_docs": len(docs),
                "pagination_complete": True,
                "pages": [
                    {
                        "page_index": 0,
                        "start": 0,
                        "docs_returned": len(docs),
                        "path": str(page),
                        "sha256": hashlib.sha256(raw).hexdigest(),
                    }
                ],
            }
        ),
        encoding="utf-8",
    )


def test_real_eric_parser_output_is_screening_ledger_input(tmp_path: Path) -> None:
    write_query(
        tmp_path,
        "Q1",
        [
            {
                "id": "EJ123456",
                "title": "Digital Education and Sustainable Development",
                "description": "A study of digital learning for sustainability.",
                "author": ["Example, Alex"],
                "publicationdateyear": "2025",
                "subject": ["Online Learning", "Sustainable Development"],
                "publicationtype": ["Journal Articles"],
                "peerreviewed": "T",
            }
        ],
    )

    records, manifest = eric.parse_exports(tmp_path, ("Q1",))
    assert manifest["unique_eric_record_count"] == 1

    parsed = tmp_path / "real-eric-studies.jsonl"
    eric.write_jsonl(parsed, records)

    loaded = ledger.load_records(parsed)
    assert len(loaded) == 1
    assert ledger.source_identity(loaded[0]) == "ERIC:EJ123456"

    snapshot = ledger.title_abstract_snapshot(loaded[0])
    assert snapshot["title"] == "Digital Education and Sustainable Development"
    assert snapshot["abstract"] == "A study of digital learning for sustainability."
    assert snapshot["publication_type"] == ["Journal Articles"]
    assert snapshot["peer_reviewed"] == "T"
