module DASHI.Ontology.LeanWikidataContextBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)

open import DASHI.Ontology.EpistemicTrit
open import DASHI.Ontology.ContextualClaimComposition
open import DASHI.Ontology.LeanWikidataTheoremSurfaceBridge

------------------------------------------------------------------------
-- RequestProject.Provenance distinguishes asserted, sourced and reliable
-- fragments and proves the selected fragments preserve validity.  Temporal.lean
-- proves time snapshots preserve validity and only remove facts relative to the
-- full time-indexed base.  DASHI already has the right carrier for this shape:
-- a provenance-bearing claim indexed by context rather than a global Boolean.
------------------------------------------------------------------------

data LeanEvidenceSlice : Set where
  assertedSlice sourcedSlice reliableSlice temporalSlice : LeanEvidenceSlice

record LeanContextWitness : Set where
  constructor leanContextWitness
  field
    slice : LeanEvidenceSlice
    theoremContract : LeanTheoremContract
    sourceMatched : Bool
    theoremAccepted : Bool
    sourceReferences : List String

open LeanContextWitness public

contextWitnessState : LeanContextWitness → EpistemicTrit
contextWitnessState witness =
  theoremReceiptState (theoremAccepted witness) (sourceMatched witness)

contextScopedClaim : LeanContextWitness → ScopedClaim LeanEvidenceSlice
contextScopedClaim witness =
  scopedClaim
    (λ requested →
      contextWitnessState witness)
    (sourceReferences witness)

contextPreservesReferences :
  (witness : LeanContextWitness) →
  ContextualClaimComposition.references (contextScopedClaim witness)
    ≡ sourceReferences witness
contextPreservesReferences witness = refl

sourcedValidityContract : LeanTheoremContract
sourcedValidityContract = contract13

reliableValidityContract : LeanTheoremContract
reliableValidityContract = contract14

temporalSnapshotValidityContract : LeanTheoremContract
temporalSnapshotValidityContract = contract17

-- Restricting evidence to one slice never grants that slice global authority.
contextSliceCarriesGlobalTruthAuthority : LeanContextWitness → Bool
contextSliceCarriesGlobalTruthAuthority _ = false

contextSliceGlobalTruthAuthorityFalse :
  (witness : LeanContextWitness) →
  contextSliceCarriesGlobalTruthAuthority witness ≡ false
contextSliceGlobalTruthAuthorityFalse witness = refl
