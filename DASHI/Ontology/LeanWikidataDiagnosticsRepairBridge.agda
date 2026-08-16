module DASHI.Ontology.LeanWikidataDiagnosticsRepairBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)

open import DASHI.Ontology.EpistemicTrit
open import DASHI.Ontology.LeanWikidataTheoremSurfaceBridge
import DASHI.Cognition.PNF.WikidataRepairProposal as Repair

------------------------------------------------------------------------
-- RequestProject.Diagnostics proves `errors = [] ↔ valid = true` for the
-- encoded KB validity predicate.  RequestProject.Redundancy proves that a
-- redundant P279 edge can be removed while preserving validity and the derived
-- subclass/instance relations.  This bridge turns those machine-checked source
-- facts into review evidence, not autonomous edit authority.
------------------------------------------------------------------------

data LeanDiagnosticKind : Set where
  validityErrorSet : LeanDiagnosticKind
  redundantSubclassWarning : LeanDiagnosticKind
  cycleWitness : LeanDiagnosticKind
  disjointnessWitness : LeanDiagnosticKind
  danglingReferenceWitness : LeanDiagnosticKind

record LeanDiagnosticWitness : Set where
  constructor leanDiagnosticWitness
  field
    diagnosticKind : LeanDiagnosticKind
    theoremContract : LeanTheoremContract
    sourceMatched : Bool
    theoremAccepted : Bool
    evidenceReferences : List String

open LeanDiagnosticWitness public

diagnosticState : LeanDiagnosticWitness → EpistemicTrit
diagnosticState witness =
  theoremReceiptState (theoremAccepted witness) (sourceMatched witness)

validityDiagnosticContract : LeanTheoremContract
validityDiagnosticContract = contract28

redundancyPruningContract : LeanTheoremContract
redundancyPruningContract = contract29

redundancyRepairOperation : Repair.RepairOperation
redundancyRepairOperation = Repair.removeRedundantSuperclass

-- A theorem-backed redundant-edge warning licenses a *review proposal* for the
-- semantically distinct redundant-edge operation.  It is deliberately not
-- collapsed into `removeBadSuperclass`.
record LeanRedundancyRepairCandidate : Set where
  constructor leanRedundancyRepairCandidate
  field
    diagnostic : LeanDiagnosticWitness
    proposedOperation : Repair.RepairOperation

canonicalRedundancyRepairCandidate :
  LeanDiagnosticWitness → LeanRedundancyRepairCandidate
canonicalRedundancyRepairCandidate witness =
  leanRedundancyRepairCandidate witness redundancyRepairOperation

repairCandidateCarriesEditAuthority : LeanRedundancyRepairCandidate → Bool
repairCandidateCarriesEditAuthority _ = false

repairCandidateCarriesTruthAuthority : LeanRedundancyRepairCandidate → Bool
repairCandidateCarriesTruthAuthority _ = false

repairCandidateEditAuthorityFalse :
  (candidate : LeanRedundancyRepairCandidate) →
  repairCandidateCarriesEditAuthority candidate ≡ false
repairCandidateEditAuthorityFalse candidate = refl

repairCandidateTruthAuthorityFalse :
  (candidate : LeanRedundancyRepairCandidate) →
  repairCandidateCarriesTruthAuthority candidate ≡ false
repairCandidateTruthAuthorityFalse candidate = refl

repairBoundary : Repair.WikidataRepairBoundary
repairBoundary = Repair.canonicalWikidataRepairBoundary
