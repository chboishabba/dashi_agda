module DASHI.Cognition.PNF.ReopenableEvidenceFibre where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.FibreRestrictionCore as Fibre
import DASHI.Core.TypedDependencyCore as Dependency
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
-- implementation frontier; semantic refutation requires an application-supplied
-- evidence-indexed proof.  No constructor promotes either of the first two into
-- the third.
------------------------------------------------------------------------

data SuppressionState : Set where
  currentlySalient currentlySuppressed : SuppressionState

data ExecutionRetention : Set where
  retainedForExecution prunedFromExecution : ExecutionRetention

record RefutationSystem (Candidate Evidence : Set) : Set₁ where
  field
    Refutes : Evidence → Candidate → Set

open RefutationSystem public

data SemanticAdmissibility
    {Candidate Evidence : Set}
    (system : RefutationSystem Candidate Evidence)
    (candidate : Candidate) : Set where
  semanticallyOpen : SemanticAdmissibility system candidate
  semanticallyRefuted :
    (evidence : Evidence) →
    Refutes system evidence candidate →
    SemanticAdmissibility system candidate

record SeparatedCandidateState
    {Candidate Evidence : Set}
    (system : RefutationSystem Candidate Evidence) : Set where
  constructor separatedCandidateState
  field
    candidate : Candidate
    suppression : SuppressionState
    executionRetention : ExecutionRetention
    semanticAdmissibility : SemanticAdmissibility system candidate

open SeparatedCandidateState public

------------------------------------------------------------------------
-- Soft evidence reweights an arbitrary candidate fibre without changing its
-- semantic support.  The Weight carrier is application-supplied: counts,
-- rationals, constructive reals, log weights, or another exact representation
-- may be used.  Reweighting is therefore strictly weaker than refutation.
------------------------------------------------------------------------

record EvidenceReweighting (Candidate Weight : Set) : Set where
  constructor evidenceReweighting
  field
    beforeWeight : Candidate → Weight
    afterWeight : Candidate → Weight
    reweightingReceipt : String

open EvidenceReweighting public

data ReweightingRefutationPermission : Set where

reweightingAloneCannotRefute : ReweightingRefutationPermission → ⊥
reweightingAloneCannotRefute ()

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
-- TypedDependencyCore already supplies the generic state/action carrier with
-- proof-bearing precondition, postcondition and dependency receipt.  We reuse
-- that exact carrier here and add only the finite reflexive/transitive closure
-- needed to witness reopening.  A suppressed or execution-pruned candidate may
-- therefore remain semantically live and later become accessible through a
-- sequence of admissible evidence actions.
------------------------------------------------------------------------

data CorrectivePath
    {Candidate Evidence : Set}
    (system : Dependency.DependentActionSystem Candidate Evidence)
    : Candidate → Candidate → Set where
  pathRefl :
    ∀ {x} → CorrectivePath system x x
  pathStep :
    ∀ {before target}
      (evidence : Evidence) →
      (admissible : Dependency.AdmissibleAction system before evidence) →
      CorrectivePath system (Dependency.after admissible) target →
      CorrectivePath system before target

record ReopeningWitness
    {Candidate Evidence : Set}
    (system : Dependency.DependentActionSystem Candidate Evidence)
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
    reweightingIsNotRefutation :
      ReweightingRefutationPermission → ⊥
    executionOverflowIsNotSemanticAuthority :
      Bounded.OverflowSemanticPermission Bounded.executionEvidenceOnly → ⊥
    suppressionAndRefutationAreDifferentTypes : Bool
    suppressionAndRefutationAreDifferentTypesIsTrue :
      suppressionAndRefutationAreDifferentTypes ≡ true
    semanticRefutationRequiresIndexedEvidence : Bool
    semanticRefutationRequiresIndexedEvidenceIsTrue :
      semanticRefutationRequiresIndexedEvidence ≡ true
    correctiveReachabilityReusesTypedActionSystem : Bool
    correctiveReachabilityReusesTypedActionSystemIsTrue :
      correctiveReachabilityReusesTypedActionSystem ≡ true

open ReopenableEvidenceBoundary public

canonicalReopenableEvidenceBoundary : ReopenableEvidenceBoundary
canonicalReopenableEvidenceBoundary =
  reopenableEvidenceBoundary
    interferingPhaseCannotRefute
    reweightingAloneCannotRefute
    Bounded.executionOverflowHasNoSemanticPermission
    true refl
    true refl
    true refl
