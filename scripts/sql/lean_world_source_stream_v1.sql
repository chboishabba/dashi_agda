-- Source-first Lean world pilot: real bytes, bounded one-pass archive transport.
-- Separate from canonical statements and candidate theorem tables.
-- All rows are original source bytes, never declarations/kernel certificates.
CREATE TABLE IF NOT EXISTS lean_world_source_blob (
  sha256 bytea PRIMARY KEY CHECK (octet_length(sha256)=32),
  git_blob_sha1 bytea NOT NULL CHECK (octet_length(git_blob_sha1)=20),
  source_size bigint NOT NULL CHECK (source_size >= 0 AND source_size <= 8388608),
  content bytea NOT NULL,
  CONSTRAINT lean_source_exact_length CHECK (octet_length(content)=source_size)
);
CREATE TABLE IF NOT EXISTS lean_world_source_occurrence (
  repository text NOT NULL,
  revision text NOT NULL CHECK (revision ~ '^[0-9a-f]{40}$'),
  path text NOT NULL,
  sha256 bytea NOT NULL REFERENCES lean_world_source_blob(sha256),
  source_size bigint NOT NULL CHECK (source_size >= 0),
  PRIMARY KEY(repository,revision,path),
  CONSTRAINT lean_source_path_safe CHECK (
    path LIKE '%.lean' AND path !~ '(^/|//|(^|/)\\.\\.?(/|$))'
  )
);
CREATE INDEX IF NOT EXISTS lean_world_source_occurrence_content_idx
  ON lean_world_source_occurrence(sha256);
CREATE TABLE IF NOT EXISTS lean_world_source_archive (
  repository text NOT NULL,
  revision text NOT NULL CHECK (revision ~ '^[0-9a-f]{40}$'),
  source_count bigint NOT NULL CHECK(source_count >= 0),
  source_bytes bigint NOT NULL CHECK(source_bytes >= 0),
  skipped_count bigint NOT NULL CHECK(skipped_count >= 0),
  status text NOT NULL CHECK(status = 'source-complete-not-elaborated'),
  PRIMARY KEY(repository,revision),
  CONSTRAINT source_complete_no_skips CHECK(skipped_count = 0)
);
CREATE OR REPLACE FUNCTION lean_world_source_immutable()
RETURNS trigger LANGUAGE plpgsql AS $$
BEGIN
  RAISE EXCEPTION 'Lean-world original source objects are immutable';
END $$;
DO $$
DECLARE t text;
BEGIN
  FOREACH t IN ARRAY ARRAY[
      'lean_world_source_blob',
      'lean_world_source_occurrence',
      'lean_world_source_archive'
  ] LOOP
    EXECUTE format('DROP TRIGGER IF EXISTS lean_world_source_no_update ON %I', t);
    EXECUTE format('CREATE TRIGGER lean_world_source_no_update BEFORE UPDATE OR DELETE ON %I FOR EACH ROW EXECUTE FUNCTION lean_world_source_immutable()', t);
    EXECUTE format('DROP TRIGGER IF EXISTS lean_world_source_no_truncate ON %I', t);
    EXECUTE format('CREATE TRIGGER lean_world_source_no_truncate BEFORE TRUNCATE ON %I FOR EACH STATEMENT EXECUTE FUNCTION lean_world_source_immutable()', t);
  END LOOP;
END $$;
