module DASHI.Physics.Closure.NSTriadKNBKMContinuation where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Primitive using (Level; lsuc; _⊔_)

import DASHI.Physics.Closure.NSTriadKNBKMResidenceBridge as BKMBridge
import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm

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

------------------------------------------------------------------------
-- Generic downstream composition from an explicitly supplied integrated
-- residue bound.  The residue-to-projection map and both analytic model
-- maps remain parameters; no Navier--Stokes hypothesis is manufactured here.
------------------------------------------------------------------------

integratedResidueBoundToFiniteBKMIntegral :
  {ℓS ℓE ℓV ℓR : Level} →
  (continuationModel :
    NSTriadKNBKMContinuationModel {ℓS} {ℓE} {ℓV} {ℓR}) →
  {residueNormModel : ResidueNorm.ResidueNormModel} →
  (N : Nat) →
  (evidence : BKMBridge.IntegratedResidueBoundEvidence residueNormModel N) →
  (projectionFromIntegratedResidue :
    BKMBridge.IntegratedResidueBoundEvidence residueNormModel N →
    BKMBridge.NSTriadKNBKMResidenceBridgeModel.BKMProjectionSmallness
      (NSTriadKNBKMContinuationModel.bkmResidenceBridgeModel
        continuationModel)) →
  NSTriadKNBKMContinuationModel.bkmIntegralFinite continuationModel
integratedResidueBoundToFiniteBKMIntegral
  continuationModel N evidence projectionFromIntegratedResidue =
  NSTriadKNBKMContinuationModel.bkmProjectionToIntegralFinite
    continuationModel
    (projectionFromIntegratedResidue evidence)

integratedResidueBoundToContinuationHypotheses :
  {ℓS ℓE ℓV ℓR : Level} →
  (continuationModel :
    NSTriadKNBKMContinuationModel {ℓS} {ℓE} {ℓV} {ℓR}) →
  {residueNormModel : ResidueNorm.ResidueNormModel} →
  (N : Nat) →
  (evidence : BKMBridge.IntegratedResidueBoundEvidence residueNormModel N) →
  (projectionFromIntegratedResidue :
    BKMBridge.IntegratedResidueBoundEvidence residueNormModel N →
    BKMBridge.NSTriadKNBKMResidenceBridgeModel.BKMProjectionSmallness
      (NSTriadKNBKMContinuationModel.bkmResidenceBridgeModel
        continuationModel)) →
  NSTriadKNBKMContinuationModel.SmoothContinuationPast continuationModel
integratedResidueBoundToContinuationHypotheses
  continuationModel N evidence projectionFromIntegratedResidue =
  NSTriadKNBKMContinuationModel.bkmContinuation
    continuationModel
    (integratedResidueBoundToFiniteBKMIntegral
      continuationModel N evidence projectionFromIntegratedResidue)

bkmContinuationClosed : Bool
bkmContinuationClosed = false

bkmContinuationClosedIsFalse :
  bkmContinuationClosed ≡ false
bkmContinuationClosedIsFalse = refl
