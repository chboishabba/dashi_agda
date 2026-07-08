module DASHI.Physics.Closure.NSTriadKNBKMContinuation where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Level; lsuc; _⊔_)

import DASHI.Physics.Closure.NSTriadKNBKMResidenceBridge as BKMBridge

------------------------------------------------------------------------
-- BKM finite-integral and continuation surface.
--
-- This is the theorem layer after structural projection smallness:
--
--   BKMProjectionSmallness
--     => bkmIntegralFinite
--     => bkmContinuation

record NSTriadKNBKMContinuationModel
    {ℓS ℓE ℓV ℓR : Level} : Set (lsuc (ℓS ⊔ ℓE ⊔ ℓV ⊔ ℓR)) where
  field
    bkmResidenceBridgeModel :
      BKMBridge.NSTriadKNBKMResidenceBridgeModel {ℓS} {ℓE} {ℓV} {ℓR}

    bkmIntegralFinite : Set ℓR
    SmoothContinuationPast : Set ℓR

    bkmProjectionToIntegralFinite :
      BKMBridge.NSTriadKNBKMResidenceBridgeModel.BKMProjectionSmallness
        bkmResidenceBridgeModel ->
      bkmIntegralFinite

    bkmContinuation :
      bkmIntegralFinite ->
      SmoothContinuationPast

open NSTriadKNBKMContinuationModel public

bkmContinuationClosed : Bool
bkmContinuationClosed = false

bkmContinuationClosedIsFalse :
  bkmContinuationClosed ≡ false
bkmContinuationClosedIsFalse = refl
