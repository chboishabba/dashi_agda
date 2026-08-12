module DASHI.Cognition.PNF.ReopenableEvidenceFibre where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.FibreRestrictionCore as Fibre
import DASHI.Core.ProvenanceBearingQuotient as Quotient
import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Reasoning.AttractorAlignedBranchSelection as Selection
import DASHI.Cognition.PNF.BoundedExecutionCarrier as Bounded

------------------------------------------------------------------------
-- PNF compatibility name for the repository-wide canonical quotient core.
--
-- There is deliberately no second reopenable-fibre record here.  The PNF
-- layer instantiates the canonical Core.ProvenanceBearingQuotient directly.
------------------------------------------------------------------------

ReopenableFibreExtension :
  (core : Fibre.FibreRestrictionCore) → Set₁
ReopenableFibreExtension = Quotient.ProvenanceBearingQuotient

------------------------------------------------------------------------
-- Three propositions that must never be collapsed into one status field.
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
-- semantic support.  Weight is application-supplied.
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
-- Corrective reachability over the existing proof-bearing action system.
--
-- This compatibility path remains here for current PNF consumers; the generic
-- action-trace / quotient-safety theorem lives in Core.DynamicalQuotientSafety.
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
-- Bounded execution is subordinate to semantic possibility.
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
    projectionResidualIsNotErasure :
      Quotient.ProjectionSemanticErasurePermission
        Quotient.projectionReceiptOnly → ⊥
    suppressionAndRefutationAreDifferentTypes : Bool
    suppressionAndRefutationAreDifferentTypesIsTrue :
      suppressionAndRefutationAreDifferentTypes ≡ true
    semanticRefutationRequiresIndexedEvidence : Bool
    semanticRefutationRequiresIndexedEvidenceIsTrue :
      semanticRefutationRequiresIndexedEvidence ≡ true
    canonicalQuotientCoreReused : Bool
    canonicalQuotientCoreReusedIsTrue : canonicalQuotientCoreReused ≡ true

open ReopenableEvidenceBoundary public

canonicalReopenableEvidenceBoundary : ReopenableEvidenceBoundary
canonicalReopenableEvidenceBoundary =
  reopenableEvidenceBoundary
    interferingPhaseCannotRefute
    reweightingAloneCannotRefute
    Bounded.executionOverflowHasNoSemanticPermission
    Quotient.projectionReceiptCannotEraseSemantics
    true refl
    true refl
    true refl
