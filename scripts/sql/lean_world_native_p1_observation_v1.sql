-- Source-bound native Lean4export-v3 expression observations in the EXISTING
-- PostgreSQL source world. No alternative world builder or admitted proof table.
-- Hashes index byte identities; exact bytes are compared on conflict.
CREATE TABLE IF NOT EXISTS lean_world_native_p1_observation (
  repository text NOT NULL,
  revision text NOT NULL CHECK (revision ~ '^[0-9a-f]{40}$'),
  path text NOT NULL,
  declaration text NOT NULL,
  native_export_sha256 bytea NOT NULL CHECK (octet_length(native_export_sha256)=32),
  original_source_sha256 bytea NOT NULL CHECK (octet_length(original_source_sha256)=32),
  toolchain text NOT NULL CHECK (length(toolchain)>0),
  handoff_key text NOT NULL CHECK(handoff_key ~ '^[0-9a-f]{64}$'),
  dependency_closure_id text NOT NULL,
  type_exact bytea NOT NULL CHECK(octet_length(type_exact)>0 AND octet_length(type_exact)<=8388608),
  type_exact_sha256 bytea NOT NULL CHECK (octet_length(type_exact_sha256)=32),
  type_alpha bytea NOT NULL CHECK(octet_length(type_alpha)>0 AND octet_length(type_alpha)<=8388608),
  type_alpha_sha256 bytea NOT NULL CHECK (octet_length(type_alpha_sha256)=32),
  proof_exact bytea NOT NULL CHECK(octet_length(proof_exact)<=8388608),
  proof_exact_sha256 bytea,
  direct_statement_constants jsonb NOT NULL,
  direct_proof_constants jsonb NOT NULL,
  observation_sha256 bytea NOT NULL CHECK (octet_length(observation_sha256)=32),
  status text NOT NULL DEFAULT 'source-bound-projected-not-kernel-checked'
    CHECK(status='source-bound-projected-not-kernel-checked'),
  PRIMARY KEY(repository,revision,path,declaration,native_export_sha256),
  FOREIGN KEY(repository,revision,path)
    REFERENCES lean_world_source_occurrence(repository,revision,path),
  CHECK (
    (octet_length(proof_exact)=0 AND proof_exact_sha256 IS NULL) OR
    (octet_length(proof_exact)>0 AND octet_length(proof_exact_sha256)=32)
  )
);
CREATE INDEX IF NOT EXISTS lean_world_native_p1_alpha_fibre_idx
 ON lean_world_native_p1_observation (toolchain,type_alpha_sha256,repository,revision);
CREATE OR REPLACE FUNCTION lean_world_native_p1_immutable()
RETURNS trigger LANGUAGE plpgsql AS $$
BEGIN
  RAISE EXCEPTION 'native expression observations are immutable';
END $$;
DROP TRIGGER IF EXISTS lean_world_native_p1_immutable_row
 ON lean_world_native_p1_observation;
CREATE TRIGGER lean_world_native_p1_immutable_row
BEFORE UPDATE OR DELETE ON lean_world_native_p1_observation
FOR EACH ROW EXECUTE FUNCTION lean_world_native_p1_immutable();
DROP TRIGGER IF EXISTS lean_world_native_p1_immutable_truncate
 ON lean_world_native_p1_observation;
CREATE TRIGGER lean_world_native_p1_immutable_truncate
BEFORE TRUNCATE ON lean_world_native_p1_observation
FOR EACH STATEMENT EXECUTE FUNCTION lean_world_native_p1_immutable();
