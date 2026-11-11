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
