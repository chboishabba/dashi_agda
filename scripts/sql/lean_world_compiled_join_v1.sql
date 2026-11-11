-- Exact original Lean compiler-checked proof join artifacts, NOT independent
-- kernel checking and NOT same-semantic-world admission. Source originals are
-- foreign-keyed to the completed source-byte PostgreSQL world.
CREATE TABLE IF NOT EXISTS lean_world_compiled_join_batch (
  batch_sha256 bytea PRIMARY KEY CHECK (octet_length(batch_sha256)=32),
  source_compiler_sha256 bytea NOT NULL CHECK (octet_length(source_compiler_sha256)=32),
  compiler_version text NOT NULL,
  original_source_snapshots jsonb NOT NULL,
  compiled_source bytea NOT NULL,
  compiled_source_sha256 bytea NOT NULL CHECK (octet_length(compiled_source_sha256)=32),
  compiled_olean bytea NOT NULL,
  compiled_olean_sha256 bytea NOT NULL CHECK (octet_length(compiled_olean_sha256)=32),
  source_scope_count integer NOT NULL CHECK(source_scope_count > 0),
  joined_theorem_count integer NOT NULL CHECK(joined_theorem_count > 0),
  status text NOT NULL DEFAULT 'lean-compiled-original-proof-joins'
    CHECK (status='lean-compiled-original-proof-joins')
);
CREATE TABLE IF NOT EXISTS lean_world_compiled_join_module (
  batch_sha256 bytea NOT NULL REFERENCES lean_world_compiled_join_batch(batch_sha256),
  module text NOT NULL,
  original_repository text NOT NULL,
  original_revision text NOT NULL,
  original_path text NOT NULL,
  source_sha256 bytea NOT NULL CHECK (octet_length(source_sha256)=32),
  compiled_olean_sha256 bytea NOT NULL CHECK(octet_length(compiled_olean_sha256)=32),
  compiled_olean bytea NOT NULL CHECK(octet_length(compiled_olean) > 0),
  PRIMARY KEY(batch_sha256,module),
  FOREIGN KEY(original_repository,original_revision,original_path)
    REFERENCES lean_world_source_occurrence(repository,revision,path)
);
CREATE TABLE IF NOT EXISTS lean_world_compiled_join_import (
  batch_sha256 bytea NOT NULL,
  source_module text NOT NULL,
  import_module text NOT NULL,
  original_module_in_batch boolean NOT NULL,
  PRIMARY KEY(batch_sha256,source_module,import_module),
  FOREIGN KEY(batch_sha256,source_module)
    REFERENCES lean_world_compiled_join_module(batch_sha256,module)
);
CREATE TABLE IF NOT EXISTS lean_world_compiled_join_theorem (
  batch_sha256 bytea NOT NULL REFERENCES lean_world_compiled_join_batch(batch_sha256),
  join_name text NOT NULL,
  donor_name text NOT NULL,
  scope_module text NOT NULL,
  PRIMARY KEY(batch_sha256,join_name),
  FOREIGN KEY(batch_sha256,scope_module)
    REFERENCES lean_world_compiled_join_module(batch_sha256,module)
);
CREATE OR REPLACE FUNCTION lean_world_reject_compiled_join_mutation()
RETURNS trigger LANGUAGE plpgsql AS $$
BEGIN
 RAISE EXCEPTION 'original compiled proof joins are immutable';
END $$;
DO $$
DECLARE t text;
BEGIN
 FOREACH t IN ARRAY ARRAY[
   'lean_world_compiled_join_batch',
   'lean_world_compiled_join_module',
   'lean_world_compiled_join_theorem',
   'lean_world_compiled_join_import'
 ] LOOP
   EXECUTE format('DROP TRIGGER IF EXISTS lean_join_immutable_row ON %I',t);
   EXECUTE format('CREATE TRIGGER lean_join_immutable_row BEFORE UPDATE OR DELETE ON %I FOR EACH ROW EXECUTE FUNCTION lean_world_reject_compiled_join_mutation()',t);
   EXECUTE format('DROP TRIGGER IF EXISTS lean_join_immutable_truncate ON %I',t);
   EXECUTE format('CREATE TRIGGER lean_join_immutable_truncate BEFORE TRUNCATE ON %I FOR EACH STATEMENT EXECUTE FUNCTION lean_world_reject_compiled_join_mutation()',t);
 END LOOP;
END $$;
