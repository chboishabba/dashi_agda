module DASHI.Core.ObserverVisibilityExistenceNoncollapseExact where

------------------------------------------------------------------------
-- OBSERVER VISIBILITY != EXISTENCE
--
-- Generic exact owner for the ITIR/SensibLaw rule:
--
--   what a system cannot represent must not silently become what does not exist.
--
-- Existence here is any application-supplied existence/presence/status target.
-- The generic carrier has no legal, metaphysical or empirical semantics until a
-- domain bridge supplies them.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF

record VisibilityExistenceSystem
    (State Visibility Existence : Set) : Set₁ where
  constructor visibility-existence-system
  field
    visibleToObserver : State → Visibility
    existenceStatus : State → Existence

open VisibilityExistenceSystem public

record InvisibleExistenceCollision
    {State Visibility Existence : Set}
    (system : VisibilityExistenceSystem State Visibility Existence) : Set where
  constructor invisible-existence-collision
  field
    absentCase presentCase : State
    sameVisibility :
      visibleToObserver system absentCase ≡
      visibleToObserver system presentCase
    differentExistence :
      existenceStatus system absentCase ≡
      existenceStatus system presentCase → ⊥

open InvisibleExistenceCollision public

collisionGivesNonFactorability :
  ∀ {State Visibility Existence : Set}
    {system : VisibilityExistenceSystem State Visibility Existence} →
  InvisibleExistenceCollision system →
  INF.NonFactorabilityWitness
    (visibleToObserver system)
    (existenceStatus system)
collisionGivesNonFactorability collision =
  INF.nonFactorabilityWitness
    (absentCase collision)
    (presentCase collision)
    (sameVisibility collision)
    (differentExistence collision)

visibilityCannotRecoverExistence :
  ∀ {State Visibility Existence : Set}
    {system : VisibilityExistenceSystem State Visibility Existence} →
  InvisibleExistenceCollision system →
  INF.FactorsThrough
    (visibleToObserver system)
    (existenceStatus system) → ⊥
visibilityCannotRecoverExistence collision =
  INF.witnessRulesOutEveryFlatFactorisation
    (collisionGivesNonFactorability collision)

visibilityRechartingStillCannotRecoverExistence :
  ∀ {State Visibility Recharted Existence : Set}
    {system : VisibilityExistenceSystem State Visibility Existence} →
  InvisibleExistenceCollision system →
  (rechart : Visibility → Recharted) →
  INF.FactorsThrough
    (λ state → rechart (visibleToObserver system state))
    (existenceStatus system) → ⊥
visibilityRechartingStillCannotRecoverExistence collision rechart =
  INF.rechartingCannotRecoverErasedPhenomenon
    rechart
    (collisionGivesNonFactorability collision)

------------------------------------------------------------------------
-- Finite regression: invisible present and invisible absent collide.
------------------------------------------------------------------------

data DemoState : Set where
  invisibleAbsent : DemoState
  invisiblePresent : DemoState


data DemoVisibility : Set where
  notVisible : DemoVisibility

data DemoExistence : Set where
  absent : DemoExistence
  present : DemoExistence

demoVisibility : DemoState → DemoVisibility
demoVisibility invisibleAbsent = notVisible
demoVisibility invisiblePresent = notVisible

demoExistence : DemoState → DemoExistence
demoExistence invisibleAbsent = absent
demoExistence invisiblePresent = present

demoSystem : VisibilityExistenceSystem DemoState DemoVisibility DemoExistence
demoSystem = visibility-existence-system demoVisibility demoExistence

canonicalInvisibleExistenceCollision : InvisibleExistenceCollision demoSystem
canonicalInvisibleExistenceCollision =
  invisible-existence-collision
    invisibleAbsent
    invisiblePresent
    refl
    (λ ())

invisibleToDemoObserverDoesNotDetermineNonexistence :
  INF.FactorsThrough demoVisibility demoExistence → ⊥
invisibleToDemoObserverDoesNotDetermineNonexistence =
  visibilityCannotRecoverExistence canonicalInvisibleExistenceCollision

------------------------------------------------------------------------
-- Stronger epistemic boundary.
------------------------------------------------------------------------

record VisibilityExistenceBoundary : Set where
  constructor visibility-existence-boundary
  field
    invisibleImpliesNonexistent : Bool
    invisibleImpliesNonexistentIsFalse : invisibleImpliesNonexistent ≡ false
    representedImpliesConstitutedByObserver : Bool
    representedImpliesConstitutedByObserverIsFalse :
      representedImpliesConstitutedByObserver ≡ false
    observerFailureChangesExistenceByDefault : Bool
    observerFailureChangesExistenceByDefaultIsFalse :
      observerFailureChangesExistenceByDefault ≡ false
    posthocRelabellingRepairsInvisibleExistenceCollision : Bool
    posthocRelabellingRepairsInvisibleExistenceCollisionIsFalse :
      posthocRelabellingRepairsInvisibleExistenceCollision ≡ false
    richerObservationMayBeRequired : Bool
    richerObservationMayBeRequiredIsTrue : richerObservationMayBeRequired ≡ true

open VisibilityExistenceBoundary public

canonicalVisibilityExistenceBoundary : VisibilityExistenceBoundary
canonicalVisibilityExistenceBoundary = visibility-existence-boundary
  false refl
  false refl
  false refl
  false refl
  true refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data InvisibleMeansNonexistent : Set where
data CategoryAbsenceMeansWorldAbsence : Set where
data RecognitionCreatesExistence : Set where

invisibleDoesNotMeanNonexistent : InvisibleMeansNonexistent → ⊥
invisibleDoesNotMeanNonexistent ()

categoryAbsenceDoesNotMeanWorldAbsence : CategoryAbsenceMeansWorldAbsence → ⊥
categoryAbsenceDoesNotMeanWorldAbsence ()

recognitionDoesNotCreateExistenceByDefault : RecognitionCreatesExistence → ⊥
recognitionDoesNotCreateExistenceByDefault ()
