-- Candidate-only original Lean DAG persistence; NOT kernel certification.
-- Run after lean_world_fibre_search_v1.sql, in the same isolated schema.
CREATE TABLE IF NOT EXISTS lean_world_candidate_receipt (
  repository text NOT NULL,
  revision text NOT NULL,
  declaration text NOT NULL,
  source_path text NOT NULL,
  source_sha256 text NOT NULL CHECK (source_sha256 ~ '^[0-9a-f]{64}$'),
  exporter_profile text NOT NULL,
  status text NOT NULL DEFAULT 'candidate-unverified'
    CHECK (status = 'candidate-unverified'),
  PRIMARY KEY (repository, revision, declaration),
  FOREIGN KEY (repository, revision, declaration)
    REFERENCES lean_world_occurrence(repository,revision,declaration)
    DEFERRABLE INITIALLY DEFERRED
);
CREATE TABLE IF NOT EXISTS lean_world_candidate_dependency (
  repository text NOT NULL,
  revision text NOT NULL,
  declaration text NOT NULL,
  dep_repository text NOT NULL,
  dep_revision text NOT NULL,
  dep_declaration text NOT NULL,
  PRIMARY KEY (repository,revision,declaration,
               dep_repository,dep_revision,dep_declaration),
  FOREIGN KEY (repository,revision,declaration)
    REFERENCES lean_world_occurrence(repository,revision,declaration)
    DEFERRABLE INITIALLY DEFERRED,
  FOREIGN KEY (dep_repository,dep_revision,dep_declaration)
    REFERENCES lean_world_occurrence(repository,revision,declaration)
    DEFERRABLE INITIALLY DEFERRED,
  CHECK ((repository,revision,declaration) <>
         (dep_repository,dep_revision,dep_declaration))
);
-- The tables intentionally have NO kernel_certified boolean that may
-- accidentally be set by ingesting an untrusted export row. Promotion requires
-- an independently reviewed, separate authenticated-checker ledger.

-- A stored original candidate receipt or dependency history is append-only.
-- Provenance corrections must create a newly pinned original identity.
CREATE OR REPLACE FUNCTION lean_world_reject_candidate_mutation()
RETURNS trigger LANGUAGE plpgsql AS $$
BEGIN
  RAISE EXCEPTION 'Lean-world candidate provenance is immutable';
END
$$;
DROP TRIGGER IF EXISTS lean_world_candidate_receipt_immutable
  ON lean_world_candidate_receipt;
CREATE TRIGGER lean_world_candidate_receipt_immutable
BEFORE UPDATE OR DELETE ON lean_world_candidate_receipt
FOR EACH ROW EXECUTE FUNCTION lean_world_reject_candidate_mutation();
DROP TRIGGER IF EXISTS lean_world_candidate_dependency_immutable
  ON lean_world_candidate_dependency;
CREATE TRIGGER lean_world_candidate_dependency_immutable
BEFORE UPDATE OR DELETE ON lean_world_candidate_dependency
FOR EACH ROW EXECUTE FUNCTION lean_world_reject_candidate_mutation();
DROP TRIGGER IF EXISTS lean_world_candidate_receipt_no_truncate
  ON lean_world_candidate_receipt;
CREATE TRIGGER lean_world_candidate_receipt_no_truncate
BEFORE TRUNCATE ON lean_world_candidate_receipt
FOR EACH STATEMENT EXECUTE FUNCTION lean_world_reject_candidate_mutation();
DROP TRIGGER IF EXISTS lean_world_candidate_dependency_no_truncate
  ON lean_world_candidate_dependency;
CREATE TRIGGER lean_world_candidate_dependency_no_truncate
BEFORE TRUNCATE ON lean_world_candidate_dependency
FOR EACH STATEMENT EXECUTE FUNCTION lean_world_reject_candidate_mutation();
