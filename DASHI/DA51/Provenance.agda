module DASHI.DA51.Provenance where

open import Agda.Builtin.String using (String)
open import DASHI.DA51.Core using (DA51Address)

------------------------------------------------------------------------
-- Authority-neutral provenance
--
-- A DA51 address is semantic identity.  A provenance edge says which producer
-- owns an artifact about that identity.  The record intentionally carries no
-- theorem truth, ZK validity, literature authority, security severity, or
-- authorization field.
------------------------------------------------------------------------

data EvidenceKind : Set where
  proof     : EvidenceKind
  trace     : EvidenceKind
  benchmark : EvidenceKind
  source    : EvidenceKind
  receipt   : EvidenceKind

record EvidenceRef : Set where
  constructor evidence
  field
    address  : DA51Address
    producer : String
    artifact : String
    kind     : EvidenceKind

open EvidenceRef public
