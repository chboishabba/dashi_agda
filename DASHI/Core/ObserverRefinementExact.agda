module DASHI.Core.ObserverRefinementExact where

------------------------------------------------------------------------
-- OBSERVER REFINEMENT / SEPARATION
--
-- Source calibration:
-- David Blackwell, "Equivalent Comparisons of Experiments",
-- Annals of Mathematical Statistics 24(2):265--272 (1953).
-- DOI: 10.1214/aoms/1177729032.
--
-- Patrick Cousot and Radhia Cousot,
-- "Abstract interpretation: a unified lattice model for static analysis of
-- programs by construction or approximation of fixpoints", POPL 1977.
-- DOI: 10.1145/512950.512973.
--
-- The sources motivate information/refinement language.  The exact finite
-- observer theorems below are DASHI-local constructions.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.TypedDependencyCore as Dependency

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

Observer : Set → Set → Set
Observer X Value = X → Value

------------------------------------------------------------------------
-- fine refines coarse exactly when coarse factors through fine.
------------------------------------------------------------------------

record Refines
    {X Coarse Fine : Set}
    (coarse : Observer X Coarse)
    (fine : Observer X Fine) : Set₁ where
  constructor refines
  field
    factor : Fine → Coarse
    factorization : (x : X) → coarse x ≡ factor (fine x)

open Refines public

sameFineImpliesSameCoarse :
  ∀ {X Coarse Fine}
    {coarse : Observer X Coarse}
    {fine : Observer X Fine} →
  Refines coarse fine →
  ∀ {x y} → fine x ≡ fine y → coarse x ≡ coarse y
sameFineImpliesSameCoarse refinement {x} {y} sameFine =
  trans
    (factorization refinement x)
    (trans
      (cong (factor refinement) sameFine)
      (sym (factorization refinement y)))

Separating :
  ∀ {X Value : Set} →
  Observer X Value → Set
Separating observer =
  ∀ {x y} → observer x ≡ observer y → x ≡ y

record Collision
    {X Value : Set}
    (observer : Observer X Value) : Set where
  constructor collision
  field
    left right : X
    sameObservation : observer left ≡ observer right
    distinctStates : left ≢ right

open Collision public

collisionRulesOutSeparation :
  ∀ {X Value}
    {observer : Observer X Value} →
  Collision observer → Separating observer → ⊥
collisionRulesOutSeparation witness separating =
  distinctStates witness (separating (sameObservation witness))

record StrictRefinement
    {X Coarse Fine : Set}
    (coarse : Observer X Coarse)
    (fine : Observer X Fine) : Set₁ where
  constructor strictRefinement
  field
    refinement : Refines coarse fine
    coarseCollision : Collision coarse
    fineSeparatesCollision :
      fine (left coarseCollision) ≢ fine (right coarseCollision)

open StrictRefinement public

strictRefinementRulesOutCoarseSeparation :
  ∀ {X Coarse Fine}
    {coarse : Observer X Coarse}
    {fine : Observer X Fine} →
  StrictRefinement coarse fine → Separating coarse → ⊥
strictRefinementRulesOutCoarseSeparation strict =
  collisionRulesOutSeparation (coarseCollision strict)

separationAscendsAlongRefinement :
  ∀ {X Coarse Fine}
    {coarse : Observer X Coarse}
    {fine : Observer X Fine} →
  Refines coarse fine →
  Separating coarse →
  Separating fine
separationAscendsAlongRefinement refinement separating sameFine =
  separating (sameFineImpliesSameCoarse refinement sameFine)

------------------------------------------------------------------------
-- Joint observers are canonical refinements of either component.
------------------------------------------------------------------------

jointObserver :
  ∀ {X Left Right : Set} →
  Observer X Left → Observer X Right → Observer X (Left × Right)
jointObserver left right x = left x , right x

jointRefinesLeft :
  ∀ {X Left Right}
    (left : Observer X Left)
    (right : Observer X Right) →
  Refines left (jointObserver left right)
jointRefinesLeft left right =
  refines proj₁ (λ x → refl)

jointRefinesRight :
  ∀ {X Left Right}
    (left : Observer X Left)
    (right : Observer X Right) →
  Refines right (jointObserver left right)
jointRefinesRight left right =
  refines proj₂ (λ x → refl)

addedObserverDifferenceImpliesStateDifference :
  ∀ {X Value}
    {observer : Observer X Value}
    {x y : X} →
  observer x ≢ observer y → x ≢ y
addedObserverDifferenceImpliesStateDifference differs refl =
  differs refl

jointStrictlyRefinesWhenAddedObserverSplitsCollision :
  ∀ {X Coarse Added}
    (coarse : Observer X Coarse)
    (added : Observer X Added)
    {x y : X} →
  coarse x ≡ coarse y →
  added x ≢ added y →
  StrictRefinement coarse (jointObserver coarse added)
jointStrictlyRefinesWhenAddedObserverSplitsCollision coarse added {x} {y}
  sameCoarse addedDiffers =
  strictRefinement
    (jointRefinesLeft coarse added)
    (collision x y sameCoarse
      (addedObserverDifferenceImpliesStateDifference addedDiffers))
    jointDiffers
  where
    jointDiffers :
      jointObserver coarse added x ≢ jointObserver coarse added y
    jointDiffers sameJoint =
      addedDiffers (cong proj₂ sameJoint)

------------------------------------------------------------------------
-- Observation fibres retain the residual collision class explicitly.
------------------------------------------------------------------------

record ObservationFibre
    {X Value : Set}
    (observer : Observer X Value)
    (value : Value) : Set where
  constructor observationFibre
  field
    point : X
    pointProjectsToValue : observer point ≡ value

open ObservationFibre public

collisionLeftFibreMember :
  ∀ {X Value}
    {observer : Observer X Value}
    (witness : Collision observer) →
  ObservationFibre observer (observer (left witness))
collisionLeftFibreMember witness =
  observationFibre (left witness) refl

collisionRightFibreMember :
  ∀ {X Value}
    {observer : Observer X Value}
    (witness : Collision observer) →
  ObservationFibre observer (observer (left witness))
collisionRightFibreMember witness =
  observationFibre
    (right witness)
    (sym (sameObservation witness))

------------------------------------------------------------------------
-- Static observer refinement and dynamic sufficiency are separate notions.
-- If a COARSER projection is already safe for a declared future observation
-- language, every finer observer refining it is safe for that same future
-- language.  The converse is deliberately not derivable: coarsening can
-- introduce a future-language collision.
------------------------------------------------------------------------

refinementPreservesFutureLanguageSafetyUpward :
  ∀ {State Action Observation Coarse Fine}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    {coarse : Observer State Coarse}
    {fine : Observer State Fine} →
  Refines coarse fine →
  Future.FutureLanguageSafeProjection system project coarse →
  Future.FutureLanguageSafeProjection system project fine
refinementPreservesFutureLanguageSafetyUpward refinement safe =
  Future.futureLanguageSafeProjection λ sameFine →
    Future.kernelContainedInFutureEquivalence safe
      (sameFineImpliesSameCoarse refinement sameFine)
