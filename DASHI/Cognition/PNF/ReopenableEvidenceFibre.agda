module DASHI.Cognition.PNF.ReopenableEvidenceFibre where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.FibreRestrictionCore as Fibre
import DASHI.Reasoning.AttractorAlignedBranchSelection as Selection
import DASHI.Cognition.PNF.BoundedExecutionCarrier as Bounded

------------------------------------------------------------------------
-- Reopenable extension of the repository's existing FibreRestrictionCore.
--
-- FibreRestrictionCore already states the crucial epistemic boundary:
-- evidence may restrict a projected fibre without recovering the hidden
-- carrier and without promoting truth.  This extension adds exactly the datum
-- needed by ITIR's provenance-bearing quotient reading: a receipt sufficient
-- to reopen the *same* fine carrier when the application supplies one.
------------------------------------------------------------------------

record ReopenableFibreExtension
    (core : Fibre.FibreRestrictionCore) : Set₁ where
  constructor reopenableFibreExtension
  field
    Receipt : Set
    receipt : Fibre.Carrier core → Receipt
    reopen : Fibre.Surface core → Receipt → Fibre.Carrier core
    reopenExact :
      (x : Fibre.Carrier core) →
      reopen (Fibre.project core x) (receipt x) ≡ x

open ReopenableFibreExtension public

------------------------------------------------------------------------
-- Three propositions that must never be collapsed into one status field.
--
-- Suppression is evidential/attention weighting; execution retention is an
-- implementation frontier; semantic admissibility is a truth-conditional
-- property.  No constructor below promotes either of the first two into the
-- third.
------------------------------------------------------------------------

data SuppressionState : Set where
  currentlySalient currentlySuppressed : SuppressionState

data ExecutionRetention : Set where
  retainedForExecution prunedFromExecution : ExecutionRetention

data SemanticAdmissibility : Set where
  semanticallyOpen semanticallyRefuted : SemanticAdmissibility

record SeparatedCandidateState (Candidate : Set) : Set where
  constructor separatedCandidateState
  field
    candidate : Candidate
    suppression : SuppressionState
    executionRetention : ExecutionRetention
    semanticAdmissibility : SemanticAdmissibility

open SeparatedCandidateState public

-- Balanced/signed phase is evidence geometry, not refutation authority.  Reuse
-- the existing interaction directions rather than creating another ternary
-- alphabet: reinforcing / independent / interfering are the exact qualitative
-- signs already derived from the repository's wave-backed interaction layer.
data PhaseRefutationPermission : Selection.InteractionDirection → Set where

reinforcingPhaseCannotRefute :
  PhaseRefutationPermission Selection.reinforcing → ⊥
reinforcingPhaseCannotRefute ()

independentPhaseCannotRefute :
  PhaseRefutationPermission Selection.independent → ⊥
independentPhaseCannotRefute ()

interferingPhaseCannotRefute :
  PhaseRefutationPermission Selection.interfering → ⊥
interferingPhaseCannotRefute ()

------------------------------------------------------------------------
-- Corrective reachability.
--
-- A suppressed or execution-pruned candidate may remain semantically live.
-- Reopening is represented by an explicit finite evidence path.  The path is
-- typed independently of semantic refutation: low accessibility is not a proof
-- of impossibility.  Terminalisation is therefore represented by the *absence
-- of a supplied CorrectivePath*, never inferred from suppression alone.
------------------------------------------------------------------------

record EvidenceTransitionSystem
    (Candidate Evidence : Set) : Set₁ where
  field
    Step : Evidence → Candidate → Candidate → Set

open EvidenceTransitionSystem public

data CorrectivePath
    {Candidate Evidence : Set}
    (system : EvidenceTransitionSystem Candidate Evidence)
    : Candidate → Candidate → Set where
  pathRefl :
    ∀ {x} → CorrectivePath system x x
  pathStep :
    ∀ {before after target}
      (evidence : Evidence) →
      Step system evidence before after →
      CorrectivePath system after target →
      CorrectivePath system before target

record ReopeningWitness
    {Candidate Evidence : Set}
    (system : EvidenceTransitionSystem Candidate Evidence)
    (candidate liveState : Candidate) : Set where
  constructor reopeningWitness
  field
    correctivePath : CorrectivePath system candidate liveState

open ReopeningWitness public

------------------------------------------------------------------------
-- Bounded execution is kept subordinate to semantic possibility.
------------------------------------------------------------------------

record ReopenableBoundedFrontier (Candidate : Set) : Set where
  constructor reopenableBoundedFrontier
  field
    activeFrontier : Bounded.BoundedExecutionCarrier Candidate
    omittedPossibilitiesRemainSemanticallyRepresentable : Bool
    omittedPossibilitiesRemainSemanticallyRepresentableIsTrue :
      omittedPossibilitiesRemainSemanticallyRepresentable ≡ true

open ReopenableBoundedFrontier public

record ReopenableEvidenceBoundary : Set where
  constructor reopenableEvidenceBoundary
  field
    negativePhaseIsNotRefutation :
      PhaseRefutationPermission Selection.interfering → ⊥
    executionOverflowIsNotSemanticAuthority :
      Bounded.OverflowSemanticPermission Bounded.executionEvidenceOnly → ⊥
    suppressionAndRefutationAreDifferentTypes : Bool
    suppressionAndRefutationAreDifferentTypesIsTrue :
      suppressionAndRefutationAreDifferentTypes ≡ true

open ReopenableEvidenceBoundary public

canonicalReopenableEvidenceBoundary : ReopenableEvidenceBoundary
canonicalReopenableEvidenceBoundary =
  reopenableEvidenceBoundary
    interferingPhaseCannotRefute
    Bounded.executionOverflowHasNoSemanticPermission
    true refl
