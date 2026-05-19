module DASHI.Physics.Closure.ShiftContractRGObservableProjection where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong)

open import DASHI.Physics.Closure.RGObservableInvariance as RGOI
open import DASHI.Physics.Closure.ShiftContractNoncanonicalP2ControlObstruction as SCO
  using (coarseCounterexampleLeft; coarseCounterexampleRight)
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance as SCSP
  using (ShiftContractState)
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI
  using (ShiftBasin; ShiftMotif; shiftRGSurface)
open import Ontology.Hecke.Scan as HS

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

------------------------------------------------------------------------
-- Reusable projection from the full shift-contract carrier into the
-- normalized RG observable quotient surface already exposed by the shift
-- observable instance.

shiftContractObservableProjection :
  ShiftContractState → RGOI.RGObservable ShiftBasin ShiftMotif
shiftContractObservableProjection =
  RGOI.RGObservableSurface.observe shiftRGSurface

shiftContractObservableProjectionLeft :
  RGOI.RGObservable ShiftBasin ShiftMotif
shiftContractObservableProjectionLeft =
  shiftContractObservableProjection coarseCounterexampleLeft

shiftContractObservableProjectionRight :
  RGOI.RGObservable ShiftBasin ShiftMotif
shiftContractObservableProjectionRight =
  shiftContractObservableProjection coarseCounterexampleRight

shiftContractObservableProjection-separates-obstructionPair :
  shiftContractObservableProjectionLeft ≢
  shiftContractObservableProjectionRight
shiftContractObservableProjection-separates-obstructionPair eq
  with cong RGOI.RGObservable.heckeSignature eq
... | sigEq with cong HS.Sig15.b3 sigEq
... | ()
