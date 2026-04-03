module DASHI.Physics.Closure.ShiftContractEigenShadowNormalizedPackage where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong)

open import DASHI.Physics.Closure.ShiftContractCoarseObservable as SCCO
  using (MaximalCoarseObservable; π-max)
open import DASHI.Physics.Closure.ShiftContractCoarseFibreFields as SCFF
  using (eigenShadowField)
open import DASHI.Physics.Closure.ShiftContractNoncanonicalP2ControlObstruction
  using (coarseCounterexampleLeft; coarseCounterexampleRight)
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance
  using (ShiftContractState)

------------------------------------------------------------------------
-- A stronger normalized package above `π-max`.
--
-- The coarse observable is preserved as the first component, while the
-- second component records the shift-side eigen-shadow extracted from the
-- corresponding coarse fibre.

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

ShiftContractNormalizedObservable : Set
ShiftContractNormalizedObservable = MaximalCoarseObservable × (Nat × Nat)

eigenShadowOnState : ShiftContractState → Nat × Nat
eigenShadowOnState x = eigenShadowField (x , refl)

π-eigenShadow : ShiftContractState → ShiftContractNormalizedObservable
π-eigenShadow x = π-max x , eigenShadowOnState x

π-eigenShadow-refines-π-max :
  ∀ x →
  proj₁ (π-eigenShadow x) ≡ π-max x
π-eigenShadow-refines-π-max _ = refl

eigenShadow-separates-obstruction-pair :
  π-eigenShadow coarseCounterexampleLeft
    ≢
  π-eigenShadow coarseCounterexampleRight
eigenShadow-separates-obstruction-pair eq =
  eigenShadow-pair-separated (cong proj₂ eq)
  where
  eigenShadow-pair-separated :
    eigenShadowOnState coarseCounterexampleLeft
      ≢
    eigenShadowOnState coarseCounterexampleRight
  eigenShadow-pair-separated ()

record ShiftContractEigenShadowNormalizedPackage : Set₁ where
  field
    projection : ShiftContractState → ShiftContractNormalizedObservable
    refines-π-max :
      ∀ x →
      proj₁ (projection x) ≡ π-max x
    separates-obstruction-pair :
      projection coarseCounterexampleLeft
        ≢
      projection coarseCounterexampleRight

canonicalShiftContractEigenShadowNormalizedPackage :
  ShiftContractEigenShadowNormalizedPackage
canonicalShiftContractEigenShadowNormalizedPackage =
  record
    { projection = π-eigenShadow
    ; refines-π-max = π-eigenShadow-refines-π-max
    ; separates-obstruction-pair = eigenShadow-separates-obstruction-pair
    }

open ShiftContractEigenShadowNormalizedPackage public
