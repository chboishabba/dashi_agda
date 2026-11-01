module DASHI.Physics.Closure.ShiftContractMdlLevelCoarseObservable where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong)

open import DASHI.Physics.Closure.RGObservableInvariance as RGOI
open import DASHI.Physics.Closure.ShiftContractCoarseObservable as SCCO
  using (MaximalCoarseObservable; π-max)
open import DASHI.Physics.Closure.ShiftContractNoncanonicalP2ControlObstruction as OB
  using (coarseCounterexampleLeft; coarseCounterexampleRight)
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI
  using (ShiftBasin; ShiftMotif; shiftRGSurface)
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance as SCSP
  using (ShiftContractState)

------------------------------------------------------------------------
-- Minimal stronger normalized package above `π-max`.
-- The first component records the shift RG mdlLevel, while the second
-- component keeps the coarse observable package unchanged.

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

MdlLevelCoarseObservable : Set
MdlLevelCoarseObservable = Nat × MaximalCoarseObservable

mdlLevelOnState : ShiftContractState → Nat
mdlLevelOnState x =
  RGOI.RGObservable.mdlLevel
    (RGOI.RGObservableSurface.observe shiftRGSurface x)

π-mdl-max : ShiftContractState → MdlLevelCoarseObservable
π-mdl-max x = mdlLevelOnState x , π-max x

π-mdl-max-refines-π-max :
  ∀ x →
  proj₂ (π-mdl-max x) ≡ π-max x
π-mdl-max-refines-π-max _ = refl

π-mdl-max-separates-obstruction-pair :
  π-mdl-max coarseCounterexampleLeft
    ≢
  π-mdl-max coarseCounterexampleRight
π-mdl-max-separates-obstruction-pair eq with cong proj₁ eq
... | ()

record ShiftContractMdlLevelCoarseObservablePackage : Set₁ where
  field
    projection : ShiftContractState → MdlLevelCoarseObservable
    refines-π-max :
      ∀ x →
      proj₂ (projection x) ≡ π-max x
    separates-obstruction-pair :
      projection coarseCounterexampleLeft
        ≢
      projection coarseCounterexampleRight

canonicalShiftContractMdlLevelCoarseObservablePackage :
  ShiftContractMdlLevelCoarseObservablePackage
canonicalShiftContractMdlLevelCoarseObservablePackage =
  record
    { projection = π-mdl-max
    ; refines-π-max = π-mdl-max-refines-π-max
    ; separates-obstruction-pair = π-mdl-max-separates-obstruction-pair
    }

open ShiftContractMdlLevelCoarseObservablePackage public
