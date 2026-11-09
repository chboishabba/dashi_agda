-- P0 Lean world search schema (PostgreSQL 15+).
-- Only metadata/provenance indexing here; no kernel certification is implied.
-- Apply through controlled migration after reviewing existing DASHI schema.
CREATE TABLE IF NOT EXISTS lean_world_fibre (
  fibre_id bigint GENERATED ALWAYS AS IDENTITY PRIMARY KEY,
  foundation_profile text NOT NULL,
  type_head text NOT NULL,
  universe_shape text NOT NULL,
  occurrence_count bigint NOT NULL DEFAULT 0 CHECK (occurrence_count >= 0),
  UNIQUE (foundation_profile, type_head, universe_shape)
);

CREATE TABLE IF NOT EXISTS lean_world_statement (
  statement_id bigint GENERATED ALWAYS AS IDENTITY PRIMARY KEY,
  fibre_id bigint NOT NULL REFERENCES lean_world_fibre(fibre_id),
  canonical_sha256 bytea NOT NULL CHECK (octet_length(canonical_sha256) = 32),
  canonical_type bytea NOT NULL CHECK (octet_length(canonical_type) > 0),
  UNIQUE (statement_id, fibre_id)
);
-- Digest is a *candidate* key. Verify byte-for-byte canonical_type equality
-- before reusing a statement_id, even if canonical_sha256 matches.
-- Concurrent authors must lock the (fibre,digest) admission key in a transaction
-- before SELECT+INSERT, or risk inserting duplicate statement objects.
CREATE INDEX IF NOT EXISTS lean_world_statement_digest_idx
  ON lean_world_statement (fibre_id, canonical_sha256);

CREATE TABLE IF NOT EXISTS lean_world_occurrence (
  repository text NOT NULL,
  revision text NOT NULL,
  declaration text NOT NULL,
  statement_id bigint NOT NULL,
  fibre_id bigint NOT NULL,
  proof_term_digest text NOT NULL,
  attribution text NOT NULL,
  source_license text,
  PRIMARY KEY (repository, revision, declaration),
  FOREIGN KEY (statement_id, fibre_id)
    REFERENCES lean_world_statement (statement_id, fibre_id)
);
-- Per-fibre B-tree supports deterministic LIMIT/keyset paging without sorting
-- all members of a high-cardinality fibre on every retrieval.
CREATE INDEX IF NOT EXISTS lean_world_occurrence_fibre_cursor_idx
  ON lean_world_occurrence (fibre_id, repository, revision, declaration);

-- Bulk-friendly exact counts: statement-level transition tables update each
-- affected fibre ONCE PER SQL INSERT/DELETE statement, not once per row.
-- This reduces hot-row contention when COPY/batched INSERT is used.
-- An update of occurrence identity/fibre is not a supported mutation: delete
-- and reinsert in the same transaction after explicitly checking ownership.
CREATE OR REPLACE FUNCTION lean_world_count_insert_batch()
RETURNS trigger LANGUAGE plpgsql AS $$
BEGIN
  UPDATE lean_world_fibre AS f
     SET occurrence_count = f.occurrence_count + batch.n
    FROM (SELECT fibre_id, count(*)::bigint AS n FROM inserted_rows
          GROUP BY fibre_id) AS batch
   WHERE f.fibre_id = batch.fibre_id;
  RETURN NULL;
END
$$;

CREATE OR REPLACE FUNCTION lean_world_count_delete_batch()
RETURNS trigger LANGUAGE plpgsql AS $$
BEGIN
  UPDATE lean_world_fibre AS f
     SET occurrence_count = f.occurrence_count - batch.n
    FROM (SELECT fibre_id, count(*)::bigint AS n FROM removed_rows
          GROUP BY fibre_id) AS batch
   WHERE f.fibre_id = batch.fibre_id;
  RETURN NULL;
END
$$;
DROP TRIGGER IF EXISTS lean_world_occurrence_count_trigger\n  ON lean_world_occurrence;\nDROP TRIGGER IF EXISTS lean_world_occurrence_insert_count_trigger
  ON lean_world_occurrence;
DROP TRIGGER IF EXISTS lean_world_occurrence_delete_count_trigger
  ON lean_world_occurrence;
CREATE TRIGGER lean_world_occurrence_insert_count_trigger
AFTER INSERT ON lean_world_occurrence
REFERENCING NEW TABLE AS inserted_rows
FOR EACH STATEMENT EXECUTE FUNCTION lean_world_count_insert_batch();

CREATE TRIGGER lean_world_occurrence_delete_count_trigger
AFTER DELETE ON lean_world_occurrence
REFERENCING OLD TABLE AS removed_rows
FOR EACH STATEMENT EXECUTE FUNCTION lean_world_count_delete_batch();

-- Example bounded query (bind exact values, no string interpolation):
-- SELECT repository, revision, declaration, statement_id, proof_term_digest,
--        attribution
-- FROM lean_world_occurrence
-- WHERE fibre_id = $1
--   AND (repository, revision, declaration) > ($2, $3, $4)
-- ORDER BY repository, revision, declaration
-- LIMIT $5;
--
-- remaining = fibre.occurrence_count - count_before_cursor - returned_count.
-- For first page only, count_before_cursor = 0; for arbitrary later cursors,
-- exact remaining requires a maintained ordinal/materialization or COUNT of
-- prior occurrences. Do not claim O(1) exact arbitrary-page counts.
--
-- A keyset cursor must carry an immutable world snapshot/ingestion generation
-- for pagination consistency while concurrent ingestion runs.
