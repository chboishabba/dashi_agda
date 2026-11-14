from __future__ import annotations

import importlib.util
from pathlib import Path
import sys

import pytest

ROOT = Path(__file__).resolve().parents[1]
MODULE_PATH = (
    ROOT
    / "tools"
    / "slr-discourse-reconstruct"
    / "persist_fleet_r5_formal_ast_subtraction.py"
)
SPEC = importlib.util.spec_from_file_location("fleet_r5_persist", MODULE_PATH)
assert SPEC is not None and SPEC.loader is not None
M = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = M
SPEC.loader.exec_module(M)


def manifest(*, with_chat: bool = False):
    fibres = []
    for kind, count in M.EXPECTED_COUNTS.items():
        for index in range(count):
            row = {
                "fibre_ref": f"{kind}:{index:04d}",
                "classification": kind,
                "source_ast_ref": f"agda-ast:{kind}:{index:04d}",
                "chat_coordinates": [],
            }
            if with_chat and index == 0:
                row["chat_coordinates"] = [
                    {
                        "canonical_thread_id": f"thread:{kind}",
                        "message_id": f"message:{kind}",
                    }
                ]
            fibres.append(row)
    return {
        "schema": M.SCHEMA,
        "document_graph_ref": M.DOCUMENT_GRAPH_REF,
        "fibres": fibres,
    }


def test_exact_partition_is_584_44_58_and_total_686():
    validated = M.validate_manifest(manifest())
    counts = {}
    for row in validated["fibres"]:
        counts[row["classification"]] = counts.get(row["classification"], 0) + 1
    assert counts == M.EXPECTED_COUNTS
    assert len(validated["fibres"]) == 686
    assert len(validated["manifest_sha256"]) == 64


def test_manifest_hash_is_input_order_independent():
    left = manifest(with_chat=True)
    right = manifest(with_chat=True)
    right["fibres"].reverse()
    assert (
        M.validate_manifest(left)["manifest_sha256"]
        == M.validate_manifest(right)["manifest_sha256"]
    )


def test_wrong_partition_fails_closed():
    value = manifest()
    value["fibres"][-1]["classification"] = "polarity_contradiction_gap"
    with pytest.raises(M.R5PersistenceError, match="polarity_contradiction_gap count"):
        M.validate_manifest(value)


def test_duplicate_fibre_identity_fails_closed():
    value = manifest()
    value["fibres"][-1]["fibre_ref"] = value["fibres"][0]["fibre_ref"]
    with pytest.raises(M.R5PersistenceError, match="duplicate fibre_ref"):
        M.validate_manifest(value)


@pytest.mark.parametrize(
    "key",
    sorted(M.FORBIDDEN_CHAT_KEYS),
)
def test_chat_coordinate_rejects_transcript_content_fields(key):
    value = manifest()
    value["fibres"][0]["chat_coordinates"] = [
        {"message_id": "m1", key: "must-not-be-persisted"}
    ]
    with pytest.raises(M.R5PersistenceError, match="reference-only"):
        M.validate_manifest(value)


def test_chat_coordinates_are_canonicalized_and_deduplicated():
    value = manifest()
    value["fibres"][0]["chat_coordinates"] = [
        {"message_id": "m1", "canonical_thread_id": "t1"},
        {"canonical_thread_id": "t1", "message_id": "m1"},
    ]
    validated = M.validate_manifest(value)
    first = next(
        row for row in validated["fibres"]
        if row["fibre_ref"] == value["fibres"][0]["fibre_ref"]
    )
    assert first["chat_coordinates"] == [
        {"canonical_thread_id": "t1", "message_id": "m1"}
    ]


class FakeCursor:
    def __init__(self, rows):
        self.rows = rows
        self.sql = ""
        self.params = None

    def execute(self, sql, params=None):
        self.sql = sql
        self.params = params

    def fetchall(self):
        return list(self.rows)


def test_chat_coordinate_must_resolve_exactly_one_canonical_row():
    cursor = FakeCursor([(1,)])
    M._verify_chat_coordinate(
        cursor,
        columns={"canonical_thread_id", "message_id", "body"},
        coordinate={"canonical_thread_id": "t1", "message_id": "m1"},
    )
    assert "corpus.chat_archive_message" in cursor.sql
    assert '"canonical_thread_id" = %s' in cursor.sql
    assert '"message_id" = %s' in cursor.sql
    assert cursor.params == ["t1", "m1"]


@pytest.mark.parametrize("rows", [[], [(1,), (1,)]])
def test_chat_coordinate_zero_or_multiple_rows_fails(rows):
    cursor = FakeCursor(rows)
    with pytest.raises(M.R5PersistenceError, match="exactly one"):
        M._verify_chat_coordinate(
            cursor,
            columns={"message_id"},
            coordinate={"message_id": "m1"},
        )


def test_chat_coordinate_requires_a_real_table_column():
    cursor = FakeCursor([(1,)])
    with pytest.raises(M.R5PersistenceError, match="no keys present"):
        M._verify_chat_coordinate(
            cursor,
            columns={"message_id"},
            coordinate={"canonical_thread_id": "t1"},
        )


def test_schema_enforces_reference_only_and_partition_counts():
    sql = M.schema_sql()
    assert "discharged_core_knowledge_count = 584" in sql
    assert "polarity_contradiction_gap_count = 44" in sql
    assert "unformalised_formal_gap_count = 58" in sql
    assert "total_fibre_count = 686" in sql
    assert "chat_storage_mode = 'reference-only'" in sql
    assert "pnf.r5_formal_ast_subtraction_chat_ref" in sql
    for forbidden in M.FORBIDDEN_CHAT_KEYS:
        assert f"'{forbidden}'" in sql


def test_canonical_graph_ref_is_exact():
    assert M.DOCUMENT_GRAPH_REF == (
        "pnf-document-graph:"
        "d14f740cb5ec4b39f22998832691f5932bae5e527118280f648f607b57456fc7"
    )
