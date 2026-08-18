module DASHI.Core.FutureRelevantBoundaryReconstructionExact where

------------------------------------------------------------------------
-- FUTURE-SAFE SECTIONED PROJECTIONS ARE RECONSTRUCTIVE UP TO FUTURE LANGUAGE
--
-- A decision/policy observer need not reconstruct the whole fine state.  The
-- right target may instead be the canonical future-observation equivalence for
-- the declared action/observation language.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.BoundaryObservationReconstructionExact as Boundary
import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.TypedDependencyCore as Dependency

sectionedFutureSafeProjectionGivesRelevantReconstruction :
  ∀ {State Action Observation Coarse : Set}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    {coarsen : State → Coarse} →
  Future.FutureLanguageSafeProjection system project coarsen →
  Future.SectionedProjection coarsen →
  Boundary.RelevantBoundaryReconstruction
    (Future.FutureObservationEquivalent system project)
    coarsen
sectionedFutureSafeProjectionGivesRelevantReconstruction safe sectioned =
  Boundary.relevantBoundaryReconstruction
    (Future.section sectioned)
    (λ state →
      Future.kernelContainedInFutureEquivalence safe
        (Future.sectionRightInverse sectioned (coarsen state)))

------------------------------------------------------------------------
-- The canonical future-equivalence presentation is therefore not claiming
-- ontological identity.  It reconstructs a representative adequate to the
-- declared future action/observation language when a section is supplied.
------------------------------------------------------------------------

record FutureRelevantBoundary : Set where
  constructor futureRelevantBoundary
  field
    exactWholeStateReconstructionRequiredForDecisionUse : Bool
    exactWholeStateReconstructionRequiredForDecisionUseIsFalse :
      exactWholeStateReconstructionRequiredForDecisionUse ≡ false
    futureRelevantReconstructionRequiresDeclaredLanguage : Bool
    futureRelevantReconstructionRequiresDeclaredLanguageIsTrue :
      futureRelevantReconstructionRequiresDeclaredLanguage ≡ true
    sectionedFutureSafetySuppliesRelevantReconstruction : Bool
    sectionedFutureSafetySuppliesRelevantReconstructionIsTrue :
      sectionedFutureSafetySuppliesRelevantReconstruction ≡ true
    futureEquivalenceMeansUniversalWorldIdentity : Bool
    futureEquivalenceMeansUniversalWorldIdentityIsFalse :
      futureEquivalenceMeansUniversalWorldIdentity ≡ false

canonicalFutureRelevantBoundary : FutureRelevantBoundary
canonicalFutureRelevantBoundary =
  futureRelevantBoundary
    false refl
    true refl
    true refl
    false refl
