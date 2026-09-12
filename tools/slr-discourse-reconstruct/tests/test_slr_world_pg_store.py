#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
from pathlib import Path
import unittest

HERE = Path(__file__).resolve().parent
MODULE_PATH = HERE.parent / "slr_world_pg_store.py"
spec = importlib.util.spec_from_file_location("slr_world_pg_store", MODULE_PATH)
assert spec and spec.loader
store = importlib.util.module_from_spec(spec)
spec.loader.exec_module(store)


class FakeCursor:
    def __init__(self) -> None:
        self.executed: list[tuple[str, object]] = []
        self.executemany_calls: list[tuple[str, list[object]]] = []

    def execute(self, sql: str, params: object = None) -> None:
        self.executed.append((sql, params))

    def executemany(self, sql: str, rows: list[object]) -> None:
        self.executemany_calls.append((sql, rows))


class WorldPgStoreTests(unittest.TestCase):
    def test_schema_is_append_only_and_idempotent(self) -> None:
        sql = store.schema_sql()
        self.assertIn("CREATE TABLE IF NOT EXISTS slr_world_source_manifestation", sql)
        self.assertIn("CREATE TABLE IF NOT EXISTS slr_world_pnf_candidate", sql)
        self.assertIn("CREATE TABLE IF NOT EXISTS slr_world_atom", sql)
        self.assertIn("CREATE TABLE IF NOT EXISTS slr_world_iteration", sql)
        self.assertNotIn("DROP TABLE", sql.upper())
        self.assertNotIn("TRUNCATE", sql.upper())

    def test_database_url_is_read_but_never_rendered_in_receipt(self) -> None:
        receipt = store.persistence_receipt(
            database_url="postgresql://secret:password@db.example/sensiblaw",
            source_manifestations=2,
            pnf_candidates=3,
            world_atoms=4,
            route_actions=1,
            iteration_rows=1,
        )
        rendered = str(receipt)
        self.assertNotIn("secret", rendered)
        self.assertNotIn("password", rendered)
        self.assertNotIn("db.example", rendered)
        self.assertEqual(receipt["database_config_source"], "DATABASE_URL")
        self.assertFalse(receipt["postgres_persistence_is_semantic_authority"])

    def test_persist_rows_use_conflict_safe_inserts(self) -> None:
        cursor = FakeCursor()
        store.persist_rows(
            cursor,
            source_manifestations=[{
                "source_manifestation_id": "wiki:Q207:en:456",
                "source_kind": "wikipedia-article",
                "qid": "Q207",
                "language": "en",
                "revision_ref": "456",
                "source_text_sha256": "abc",
                "payload": {"candidate_only": True},
            }],
            pnf_candidates=[{
                "claim_candidate_id": "claim:1",
                "source_manifestation_id": "wiki:Q207:en:456",
                "payload": {"claim_truth_promoted": False},
            }],
            world_atoms=[{
                "atom_id": "pnf:claim:1",
                "atom_kind": "pnf-candidate",
                "subject_qid": "Q207",
                "source_manifestation_id": "wiki:Q207:en:456",
                "payload": {"candidate_only": True},
            }],
            route_actions=[{
                "action_id": "Q1:P279:Q2",
                "iteration_index": 4,
                "payload": {"frontier_rank_is_truth_rank": False},
            }],
            iteration_rows=[{
                "iteration_index": 4,
                "parent_iteration_index": 3,
                "payload": {"consumer_closure_paid": False},
            }],
        )
        self.assertGreaterEqual(len(cursor.executemany_calls), 5)
        for sql, _rows in cursor.executemany_calls:
            self.assertIn("ON CONFLICT", sql)
            self.assertNotIn("DELETE", sql.upper())


if __name__ == "__main__":
    unittest.main()
