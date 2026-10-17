{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116CanonicalSelectedTermReplayExact where

open import Agda.Builtin.Bool using (Bool; false)

------------------------------------------------------------------------
-- Canonical residual owner for the historical R409 selected-term replay lane.
-- Provenance and execution receipts are intentionally separate from the
-- proof-bearing selected-term identity.  Neither can inhabit that equality by
-- extraction alone.
------------------------------------------------------------------------

record CMP116CanonicalSelectedTermReplay
    (SourceTranscriptionReceipt
     ExecutionReplayReceipt
     SelectedTermIdentity
     ProofBearingEquality : Set) : Set₁ where
  field
    sourceTranscriptionReceipt : SourceTranscriptionReceipt
    executionReplayReceipt : ExecutionReplayReceipt
    selectedTermIdentity : SelectedTermIdentity
    proofBearingEquality : ProofBearingEquality

------------------------------------------------------------------------

open CMP116CanonicalSelectedTermReplay public

executionReplayCreatesProofEquality : Bool
executionReplayCreatesProofEquality = false

sourceTranscriptionCreatesProofEquality : Bool
sourceTranscriptionCreatesProofEquality = false
