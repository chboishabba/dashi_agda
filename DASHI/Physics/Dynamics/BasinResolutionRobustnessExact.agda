{-# OPTIONS --safe #-}
module DASHI.Physics.Dynamics.BasinResolutionRobustnessExact where

open import DASHI.Core.Prelude
import DASHI.Physics.Dynamics.SingularBasinReductionExact as SBR

record ResolutionGeometry
  (State Resolution : Set) : Set₁ where
  field
    Near : Resolution → State → State → Set

open ResolutionGeometry public

RobustAt :
  ∀ {State Resolution : Set} →
  ResolutionGeometry State Resolution →
  (State → Set) →
  Resolution →
  State →
  Set
RobustAt G Predicate δ centre =
  ∀ candidate →
  Near G δ centre candidate →
  Predicate candidate

record BasinBoundaryResolutionWitness
  {State Resolution : Set}
  (G : ResolutionGeometry State Resolution)
  (Predicate : State → Set)
  (δ : Resolution) : Set where
  field
    inside : State
    outside : State
    withinResolution :
      Near G δ inside outside
    insideHas :
      Predicate inside
    outsideLacks :
      ¬ Predicate outside

open BasinBoundaryResolutionWitness public

boundary-witness-refutes-robustness :
  ∀ {State Resolution : Set}
    {G : ResolutionGeometry State Resolution}
    {Predicate : State → Set}
    {δ : Resolution} →
  (witness : BasinBoundaryResolutionWitness G Predicate δ) →
  ¬ RobustAt G Predicate δ (inside witness)
boundary-witness-refutes-robustness witness robust =
  outsideLacks witness
    (robust
      (outside witness)
      (withinResolution witness))

record ResolutionIncludes
  {State Resolution : Set}
  (G : ResolutionGeometry State Resolution)
  (fine coarse : Resolution) : Set where
  field
    includes :
      ∀ x y →
      Near G fine x y →
      Near G coarse x y

open ResolutionIncludes public

boundary-witness-weaken :
  ∀ {State Resolution : Set}
    {G : ResolutionGeometry State Resolution}
    {Predicate : State → Set}
    {fine coarse : Resolution} →
  ResolutionIncludes G fine coarse →
  BasinBoundaryResolutionWitness G Predicate fine →
  BasinBoundaryResolutionWitness G Predicate coarse
boundary-witness-weaken inclusion witness =
  record
    { inside = inside witness
    ; outside = outside witness
    ; withinResolution =
        includes inclusion
          (inside witness)
          (outside witness)
          (withinResolution witness)
    ; insideHas = insideHas witness
    ; outsideLacks = outsideLacks witness
    }

ResolutionAdequateForPredicate :
  ∀ {State Observable Resolution : Set} →
  ResolutionGeometry State Resolution →
  (State → Observable) →
  (State → Set) →
  Resolution →
  Set
ResolutionAdequateForPredicate G observe Predicate δ =
  ∀ x y →
  Near G δ x y →
  observe x ≡ observe y →
  SBR.LogicalEquivalence (Predicate x) (Predicate y)

record SameObservationBoundaryWitness
  {State Observable Resolution : Set}
  (G : ResolutionGeometry State Resolution)
  (observe : State → Observable)
  (Predicate : State → Set)
  (δ : Resolution) : Set where
  field
    inside : State
    outside : State
    withinResolution :
      Near G δ inside outside
    sameObservation :
      observe inside ≡ observe outside
    insideHas :
      Predicate inside
    outsideLacks :
      ¬ Predicate outside

open SameObservationBoundaryWitness public

same-observation-boundary-refutes-resolution-adequacy :
  ∀ {State Observable Resolution : Set}
    {G : ResolutionGeometry State Resolution}
    {observe : State → Observable}
    {Predicate : State → Set}
    {δ : Resolution} →
  SameObservationBoundaryWitness G observe Predicate δ →
  ¬ ResolutionAdequateForPredicate G observe Predicate δ
same-observation-boundary-refutes-resolution-adequacy witness adequate =
  outsideLacks witness
    (SBR.LogicalEquivalence.forward
      (adequate
        (inside witness)
        (outside witness)
        (withinResolution witness)
        (sameObservation witness))
      (insideHas witness))

same-observation-boundary-gives-projection-collision :
  ∀ {State Observable Resolution : Set}
    {G : ResolutionGeometry State Resolution}
    {observe : State → Observable}
    {Predicate : State → Set}
    {δ : Resolution} →
  SameObservationBoundaryWitness G observe Predicate δ →
  SBR.ProjectionPredicateCollision observe Predicate
same-observation-boundary-gives-projection-collision witness =
  record
    { left = inside witness
    ; right = outside witness
    ; sameProjection = sameObservation witness
    ; leftHas = insideHas witness
    ; rightLacks = outsideLacks witness
    }

same-observation-boundary-refutes-global-factorisation :
  ∀ {State Observable Resolution : Set}
    {G : ResolutionGeometry State Resolution}
    {observe : State → Observable}
    {Predicate : State → Set}
    {δ : Resolution} →
  SameObservationBoundaryWitness G observe Predicate δ →
  ¬ SBR.PredicateFactorisation observe Predicate
same-observation-boundary-refutes-global-factorisation witness =
  SBR.collision-refutes-factorisation
    (same-observation-boundary-gives-projection-collision witness)

record BasinSelectionSensitivity
  {State Resolution : Set}
  (G : ResolutionGeometry State Resolution)
  (Predicate : State → Set) : Set₁ where
  field
    selectedResolution : Resolution
    boundaryWitness :
      BasinBoundaryResolutionWitness
        G Predicate selectedResolution

open BasinSelectionSensitivity public
