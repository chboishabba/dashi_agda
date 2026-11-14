module DASHI.DA51.ProvenanceRevision where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Maybe using (Maybe)
open import Agda.Builtin.String using (String)
open import DASHI.DA51.Provenance using (EvidenceRef)

record EvidenceRevisionRef : Set where
  constructor evidenceRevision
  field
    evidenceRef      : EvidenceRef
    artifactRevision : String
    artifactDigest   : String
    statementDigest  : String
    demandRef        : Maybe String
    obligationRef    : Maybe String

open EvidenceRevisionRef public

establishesProof : EvidenceRevisionRef → Bool
establishesProof _ = false
