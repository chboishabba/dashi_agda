#!/usr/bin/env python3
"""Actual PostgreSQL 15+ migration and data-integrity gate, no CI dependency.

Requires psql and access to a TEST database via standard PG* env vars.
Creates an isolated temporary schema, applies migration TWICE, checks
statement-level counts, immutable provenance, composite FK, idempotence and
keyset. Does not modify existing world tables. Drops schema in finally.

  PGDATABASE=dashi_test python3 -m unittest tests/test_lean_world_postgres_migration.py -v
"""
from __future__ import annotations
import os
from pathlib import Path
import shutil
import subprocess
import unittest
from uuid import uuid4

SQL = Path(__file__).resolve().parents[1] / "scripts/sql/lean_world_fibre_search_v1.sql"


def psql(sql: str | None = None, *, filename: Path | None = None,
         env: dict | None = None) -> str:
    cmd = ["psql", "-X", "-v", "ON_ERROR_STOP=1", "-qAt"]
    if filename is not None:
        cmd += ["-f", str(filename)]
    else:
        cmd += ["-c", sql or ""]
    completed = subprocess.run(cmd, env=env, text=True, capture_output=True,
                               check=False, timeout=60)
    if completed.returncode:
        raise AssertionError(
            "PostgreSQL command failed (stderr only): " + completed.stderr[-2500:])
    return completed.stdout.strip()


class PostgreSQLMigration(unittest.TestCase):
    def test_actual_migration_counters_and_rejections(self):
        if not shutil.which("psql"):
            self.skipTest("psql unavailable: a live PostgreSQL migration was NOT validated")
        if not os.environ.get("PGDATABASE"):
            self.skipTest("PGDATABASE not configured for an isolated test database")
        schema = "lwtest_" + uuid4().hex
        raw_env = os.environ.copy()
        env = dict(raw_env, PGOPTIONS=f"-c search_path={schema},public")
        psql(f"CREATE SCHEMA {schema}", env=raw_env)
        try:
            psql(filename=SQL, env=env)
            psql(filename=SQL, env=env)  # migration must be idempotent
            query = r"""
DO $$
DECLARE f1 bigint; f2 bigint; s1 bigint; s2 bigint; n bigint;
BEGIN
  INSERT INTO lean_world_fibre(foundation_profile,type_head,universe_shape)
    VALUES('lean4@pinned','Eq','u0') RETURNING fibre_id INTO f1;
  INSERT INTO lean_world_fibre(foundation_profile,type_head,universe_shape)
    VALUES('lean4@pinned','Iff','u0') RETURNING fibre_id INTO f2;
  INSERT INTO lean_world_statement(fibre_id,canonical_sha256,canonical_type)
    VALUES(f1,decode(repeat('ab',32),'hex'),convert_to('type-A','utf8'))
    RETURNING statement_id INTO s1;
  INSERT INTO lean_world_statement(fibre_id,canonical_sha256,canonical_type)
    VALUES(f2,decode(repeat('cd',32),'hex'),convert_to('type-B','utf8'))
    RETURNING statement_id INTO s2;

  INSERT INTO lean_world_occurrence
    (repository,revision,declaration,statement_id,fibre_id,proof_term_digest,attribution)
    VALUES
      ('r','rev','A',s1,f1,'term-a','author-a'),
      ('r','rev','B',s1,f1,'term-b','author-b'),
      ('r','rev','C',s1,f1,'term-c','author-c'),
      ('r','rev','D',s2,f2,'term-d','author-d');

  IF (SELECT occurrence_count FROM lean_world_fibre WHERE fibre_id=f1) <> 3 THEN
    RAISE EXCEPTION 'batch insert failed per-fibre count';
  END IF;
  IF (SELECT occurrence_count FROM lean_world_fibre WHERE fibre_id=f2) <> 1 THEN
    RAISE EXCEPTION 'batch insert failed second fibre count';
  END IF;

  DELETE FROM lean_world_occurrence WHERE repository='r' AND declaration IN ('B','C');
  IF (SELECT occurrence_count FROM lean_world_fibre WHERE fibre_id=f1) <> 1 THEN
    RAISE EXCEPTION 'batch delete count mismatch';
  END IF;

  BEGIN
    UPDATE lean_world_occurrence SET fibre_id=f2
      WHERE repository='r' AND declaration='A';
    RAISE EXCEPTION 'UPDATE incorrectly admitted';
  EXCEPTION WHEN raise_exception THEN
    IF SQLERRM = 'UPDATE incorrectly admitted' THEN RAISE; END IF;
  END;

  BEGIN
    INSERT INTO lean_world_occurrence
      (repository,revision,declaration,statement_id,fibre_id,proof_term_digest,attribution)
      VALUES('r','rev','wrong-fibre',s1,f2,'term-w','author-w');
    RAISE EXCEPTION 'composite foreign key failed';
  EXCEPTION WHEN foreign_key_violation THEN NULL; END;

  BEGIN
    INSERT INTO lean_world_occurrence
      (repository,revision,declaration,statement_id,fibre_id,proof_term_digest,attribution)
      VALUES('r','rev','A',s1,f1,'different-term','different-author');
    RAISE EXCEPTION 'duplicate origin incorrectly admitted';
  EXCEPTION WHEN unique_violation THEN NULL; END;

  SELECT count(*) INTO n
  FROM (
    SELECT repository, revision, declaration
    FROM lean_world_occurrence
    WHERE fibre_id=f1 AND (repository, revision, declaration)>('r','rev','A')
    ORDER BY repository, revision, declaration LIMIT 10
  ) q;
  IF n<>0 THEN RAISE EXCEPTION 'keyset cursor inconsistent'; END IF;
  IF (SELECT occurrence_count FROM lean_world_fibre WHERE fibre_id=f1)<>1 THEN
    RAISE EXCEPTION 'failed statements changed stored count';
  END IF;
END
$$;
"""
            psql(query, env=env)
            self.assertEqual(
                psql("SELECT occurrence_count FROM lean_world_fibre "
                     "ORDER BY type_head", env=env).splitlines(), ["1", "1"])
        finally:
            psql(f"DROP SCHEMA {schema} CASCADE", env=raw_env)


if __name__ == "__main__":
    unittest.main()
