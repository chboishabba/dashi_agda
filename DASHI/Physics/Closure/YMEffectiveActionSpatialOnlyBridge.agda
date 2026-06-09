module DASHI.Physics.Closure.YMEffectiveActionSpatialOnlyBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.YMEffectiveActionSupportInterface as Support

------------------------------------------------------------------------
-- Typed Gate-B bridge.
--
-- Sprint 81C defined the support interface.  This module records the first
-- theorem assembly over that interface: if residual effective-action support
-- evidence is supplied, then the A1 spatial-support theorem follows.  The
-- evidence itself is still the analytic transfer-absorption theorem and is not
-- derived here.

record ResidualEffectiveActionSpatialSupportEvidence : Set₁ where
  field
    residualSpatialSupport :
      (S : Support.BalabanEffectiveAction) →
      (γ : Support.Polymer) →
      Support.PolymerIn S γ →
      Support.SpatialSupport γ

open ResidualEffectiveActionSpatialSupportEvidence public

effectiveActionPolymersSpatialOnlyForA1FromEvidence :
  ResidualEffectiveActionSpatialSupportEvidence →
  Support.EffectiveActionPolymersSpatialOnlyForA1Theorem
effectiveActionPolymersSpatialOnlyForA1FromEvidence evidence =
  record
    { provesSpatialSupport = residualSpatialSupport evidence
    }

blockedL2SpatialGraphFromSpatialOnly :
  Support.EffectiveActionPolymersSpatialOnlyForA1Theorem →
  Support.PolymerDefinedOnBlockedLatticeTheorem →
  (S : Support.BalabanEffectiveAction) →
  (γ : Support.Polymer) →
  Support.PolymerIn S γ →
  Support.DefinedOnBlockedL2SpatialGraph γ
blockedL2SpatialGraphFromSpatialOnly spatialOnly blockedTheorem S γ member =
  Support.PolymerDefinedOnBlockedLatticeTheorem.provesBlockedL2SpatialGraph
    blockedTheorem
    γ
    (Support.EffectiveActionPolymersSpatialOnlyForA1Theorem.provesSpatialSupport
      spatialOnly
      S
      γ
      member)

record GateBSpatialOnlyBridgeDefined : Set₂ where
  field
    supportInterfaceDefined :
      Support.GateBSupportInterfaceDefined
    residualSupportEvidenceCarrierDefined :
      ResidualEffectiveActionSpatialSupportEvidence
        ≡ ResidualEffectiveActionSpatialSupportEvidence
    effectiveActionSpatialOnlyAssemblyDefined :
      effectiveActionPolymersSpatialOnlyForA1FromEvidence
        ≡ effectiveActionPolymersSpatialOnlyForA1FromEvidence
    blockedL2BridgeDefined :
      blockedL2SpatialGraphFromSpatialOnly
        ≡ blockedL2SpatialGraphFromSpatialOnly

gateBSpatialOnlyBridgeDefined : GateBSpatialOnlyBridgeDefined
gateBSpatialOnlyBridgeDefined =
  record
    { supportInterfaceDefined = Support.gateBSupportInterfaceDefined
    ; residualSupportEvidenceCarrierDefined = refl
    ; effectiveActionSpatialOnlyAssemblyDefined = refl
    ; blockedL2BridgeDefined = refl
    }

residualEffectiveActionSpatialSupportEvidenceProved : Bool
residualEffectiveActionSpatialSupportEvidenceProved = false

effectiveActionPolymersSpatialOnlyForA1Unconditional : Bool
effectiveActionPolymersSpatialOnlyForA1Unconditional = false

polymerDefinedOnBlockedLatticeUnconditional : Bool
polymerDefinedOnBlockedLatticeUnconditional = false

kpEntropyAtBlockedScaleL2Unconditional : Bool
kpEntropyAtBlockedScaleL2Unconditional = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

data GateBSpatialOnlyBridgePromotion : Set where

gateBSpatialOnlyBridgePromotionImpossibleHere :
  GateBSpatialOnlyBridgePromotion →
  ⊥
gateBSpatialOnlyBridgePromotionImpossibleHere ()

record GateBSpatialOnlyBridgeBoundary : Set₂ where
  field
    bridgeDefined :
      GateBSpatialOnlyBridgeDefined
    residualSupportEvidenceStillOpen :
      residualEffectiveActionSpatialSupportEvidenceProved ≡ false
    effectiveActionSpatialOnlyStillConditional :
      effectiveActionPolymersSpatialOnlyForA1Unconditional ≡ false
    blockedLatticeStillConditional :
      polymerDefinedOnBlockedLatticeUnconditional ≡ false
    kpEntropyStillOpen :
      kpEntropyAtBlockedScaleL2Unconditional ≡ false
    noClayPromotion :
      clayYangMillsPromoted ≡ false
    noPromotionPossibleHere :
      GateBSpatialOnlyBridgePromotion → ⊥

gateBSpatialOnlyBridgeBoundary : GateBSpatialOnlyBridgeBoundary
gateBSpatialOnlyBridgeBoundary =
  record
    { bridgeDefined = gateBSpatialOnlyBridgeDefined
    ; residualSupportEvidenceStillOpen = refl
    ; effectiveActionSpatialOnlyStillConditional = refl
    ; blockedLatticeStillConditional = refl
    ; kpEntropyStillOpen = refl
    ; noClayPromotion = refl
    ; noPromotionPossibleHere = gateBSpatialOnlyBridgePromotionImpossibleHere
    }
