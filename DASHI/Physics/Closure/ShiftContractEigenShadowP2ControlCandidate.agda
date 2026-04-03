module DASHI.Physics.Closure.ShiftContractEigenShadowP2ControlCandidate where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong)

open import DASHI.Physics.Closure.ShiftContractCoarseObservable as SCCO
  using (MaximalCoarseObservable; π-max)
open import DASHI.Physics.Closure.ShiftContractEigenShadowNormalizedPackage as SENP
  using
    ( ShiftContractNormalizedObservable
    ; eigenShadowOnState
    ; π-eigenShadow
    ; π-eigenShadow-refines-π-max
    ; eigenShadow-separates-obstruction-pair
    )
open import DASHI.Physics.Closure.ShiftContractNoncanonicalP2ControlObstruction as OB
  using
    ( coarseCounterexampleLeft
    ; coarseCounterexampleRight
    ; sameCoarseObservable
    )
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance
  using (ShiftContractState)

------------------------------------------------------------------------
-- Fallback noncanonical control candidate.
--
-- The stronger package `eigenShadow × π-max` does not yield a p2-control
-- theorem for the old coarse quotient, but it does give a narrow normalized
-- control surface of its own and it is strictly finer than `π-max`.

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

eigenShadow-controls-coarse :
  ∀ x y →
  π-eigenShadow x ≡ π-eigenShadow y →
  π-max x ≡ π-max y
eigenShadow-controls-coarse _ _ eq = cong proj₁ eq

eigenShadow-controls-shadow :
  ∀ x y →
  π-eigenShadow x ≡ π-eigenShadow y →
  eigenShadowOnState x ≡ eigenShadowOnState y
eigenShadow-controls-shadow _ _ eq = cong proj₂ eq

eigenShadowP2Candidate-strictly-refines-π-max :
  π-eigenShadow coarseCounterexampleLeft
    ≢
  π-eigenShadow coarseCounterexampleRight
eigenShadowP2Candidate-strictly-refines-π-max =
  eigenShadow-separates-obstruction-pair

eigenShadowP2Candidate-not-through-π-max :
  (∀ x y → π-max x ≡ π-max y → π-eigenShadow x ≡ π-eigenShadow y) →
  ⊥
eigenShadowP2Candidate-not-through-π-max through =
  eigenShadowP2Candidate-strictly-refines-π-max
    (through
      coarseCounterexampleLeft
      coarseCounterexampleRight
      sameCoarseObservable)

record ShiftContractEigenShadowP2ControlCandidate : Set₁ where
  field
    projection : ShiftContractState → ShiftContractNormalizedObservable
    refines-π-max :
      ∀ x →
      proj₁ (projection x) ≡ π-max x
    coarse-controls :
      ∀ x y →
      projection x ≡ projection y →
      π-max x ≡ π-max y
    shadow-controls :
      ∀ x y →
      projection x ≡ projection y →
      eigenShadowOnState x ≡ eigenShadowOnState y
    separates-obstruction-pair :
      projection coarseCounterexampleLeft
        ≢
      projection coarseCounterexampleRight

canonicalShiftContractEigenShadowP2ControlCandidate :
  ShiftContractEigenShadowP2ControlCandidate
canonicalShiftContractEigenShadowP2ControlCandidate =
  record
    { projection = π-eigenShadow
    ; refines-π-max = π-eigenShadow-refines-π-max
    ; coarse-controls = eigenShadow-controls-coarse
    ; shadow-controls = eigenShadow-controls-shadow
    ; separates-obstruction-pair = eigenShadow-separates-obstruction-pair
    }

open ShiftContractEigenShadowP2ControlCandidate public
