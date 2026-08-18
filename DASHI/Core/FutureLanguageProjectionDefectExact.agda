module DASHI.Core.FutureLanguageProjectionDefectExact where

------------------------------------------------------------------------
-- FUTURE-LANGUAGE PROJECTION DEFECT
--
-- DynamicalQuotientSafety.TerminalisationDefect uses one projection both as
-- the present quotient and as the future observation.  The stronger
-- FutureObservationLanguageQuotientExact API deliberately separates these:
--
--   coarsen : State -> Coarse
--   project : State -> Observation.
--
-- This record supplies the corresponding negative witness: two states collide
-- under the current coarse observer but differ in the declared future
-- observation language after the same action trace.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.TypedDependencyCore as Dependency

record FutureLanguageProjectionDefect
    {State Action Observation Coarse : Set}
    (system : Dependency.DependentActionSystem State Action)
    (project : State → Observation)
    (coarsen : State → Coarse) : Set₁ where
  constructor futureLanguageProjectionDefect
  field
    left right : State
    sameCurrentCoarse : coarsen left ≡ coarsen right
    actionTrace : List Action
    futureObservationValue : Observation
    rightFutureWitness :
      Future.FutureObservation
        system project right actionTrace futureObservationValue
    leftFutureImpossible :
      Future.FutureObservation
        system project left actionTrace futureObservationValue → ⊥

open FutureLanguageProjectionDefect public

futureLanguageDefectContradictsSafety :
  ∀ {State Action Observation Coarse}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    {coarsen : State → Coarse} →
  Future.FutureLanguageSafeProjection system project coarsen →
  FutureLanguageProjectionDefect system project coarsen →
  ⊥
futureLanguageDefectContradictsSafety safe defect =
  leftFutureImpossible defect
    (Future.backward
      (Future.sameFutureLanguage
        (Future.kernelContainedInFutureEquivalence safe
          (sameCurrentCoarse defect))
        (actionTrace defect)
        (futureObservationValue defect))
      (rightFutureWitness defect))

record FutureLanguageProjectionDefectBoundary : Set where
  constructor futureLanguageProjectionDefectBoundary
  field
    currentCoarseningAndFutureObservationSeparated : Bool
    currentCoarseningAndFutureObservationSeparatedIsTrue :
      currentCoarseningAndFutureObservationSeparated ≡ true
    oneFutureLanguageCollisionBlocksSafety : Bool
    oneFutureLanguageCollisionBlocksSafetyIsTrue :
      oneFutureLanguageCollisionBlocksSafety ≡ true
    defectMeansUnreopenableCollapse : Bool
    defectMeansUnreopenableCollapseIsFalse :
      defectMeansUnreopenableCollapse ≡ false

canonicalFutureLanguageProjectionDefectBoundary :
  FutureLanguageProjectionDefectBoundary
canonicalFutureLanguageProjectionDefectBoundary =
  futureLanguageProjectionDefectBoundary true refl true refl false refl
