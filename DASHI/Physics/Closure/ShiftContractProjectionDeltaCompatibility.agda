module DASHI.Physics.Closure.ShiftContractProjectionDeltaCompatibility where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.RGObservableInvariance as RGOI
open import DASHI.Physics.Closure.ShiftContractObservableTransportPrimeCompatibilityProfileInstance as SCOT
  using
    ( ShiftContractObservable
    ; shiftContractTransportedProjectionDeltaCompatibility
    )
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance as SCSP
  using (ShiftContractState)

------------------------------------------------------------------------
-- Re-export the first genuinely noncanonical projection/Δ witness through the
-- bundle-owned transported theorem layer so broader recovery surfaces can
-- consume the owner module directly.

shiftContractProjectionDeltaCompatibility :
  RGOI.ProjectionDeltaCompatibility
    ShiftContractState
    ShiftContractObservable
    _≡_
shiftContractProjectionDeltaCompatibility =
  shiftContractTransportedProjectionDeltaCompatibility
