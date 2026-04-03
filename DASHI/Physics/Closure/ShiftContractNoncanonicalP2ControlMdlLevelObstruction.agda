module DASHI.Physics.Closure.ShiftContractNoncanonicalP2ControlMdlLevelObstruction where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (cong)

open import DASHI.Physics.Closure.RGObservableInvariance as RGOI
open import DASHI.Physics.Closure.ShiftContractCoarseObservable as SCCO
open import DASHI.Physics.Closure.ShiftContractNoncanonicalP2ControlObstruction as OB
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance as SCSP
  using (ShiftContractState)

------------------------------------------------------------------------
-- Cheapest stronger package above π-max: add the shift RG mdlLevel channel.
-- The current obstruction pair is already separated here, so the old coarse
-- obstruction does not extend unchanged above π-max.  This still does not
-- provide a positive p2-style control theorem on the full shift-contract
-- carrier.

MdlLevelMaximalCoarseObservable : Set
MdlLevelMaximalCoarseObservable = Nat × SCCO.MaximalCoarseObservable

π-mdl-max : ShiftContractState → MdlLevelMaximalCoarseObservable
π-mdl-max x =
  RGOI.RGObservable.mdlLevel
    (RGOI.RGObservableSurface.observe SRGOI.shiftRGSurface x)
  , SCCO.π-max x

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

π-mdl-max-separates-obstruction-pair :
  π-mdl-max OB.coarseCounterexampleLeft
    ≢
  π-mdl-max OB.coarseCounterexampleRight
π-mdl-max-separates-obstruction-pair eq with cong proj₁ eq
... | ()
