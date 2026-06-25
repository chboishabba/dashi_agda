module DASHI.Physics.YangMills.BalabanRGLane where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Geometry.Gauge.SUNPrimitives
open import DASHI.Physics.Closure.BalabanRGMassGapReceiptSurface using
  ( BalabanRGMassGapReceiptSurface
  ; canonicalBalabanRGMassGapReceiptSurface
  )
open import DASHI.Physics.YangMills.BalabanRGStepVLane using
  ( BalabanRGLaneState
  ; currentBalabanRGLaneState
  )
open import DASHI.Physics.YangMills.BalabanGaugeFixingCompatibilityGate using
  ( GaugeFixingCompatibilityGate
  ; currentGaugeFixingCompatibilityGate
  )
open import DASHI.Physics.YangMills.BalabanContinuumStabilityGate using
  ( ContinuumStabilityGate
  ; currentContinuumStabilityGate
  )

data BalabanRGLaneObligation : Set where
  needsGaugeFixingCompatibility  : BalabanRGLaneObligation
  needsContinuumStability        : BalabanRGLaneObligation

canonicalBalabanRGLaneObligations : List BalabanRGLaneObligation
canonicalBalabanRGLaneObligations =
  needsGaugeFixingCompatibility
  ∷ needsContinuumStability
  ∷ []

record BalabanRGLane : Setω where
  field
    receiptSurface : BalabanRGMassGapReceiptSurface
    stepVState : BalabanRGLaneState
    gaugeFixingGate : GaugeFixingCompatibilityGate
    continuumGate : ContinuumStabilityGate
    blockSizeDefined : Bool
    effectiveActionDefined : Bool
    blockMapDefined : Bool
    smallLargeFieldSplitDefined : Bool
    blockSizeDefinedIsTrue : blockSizeDefined ≡ true
    effectiveActionDefinedIsTrue : effectiveActionDefined ≡ true
    blockMapDefinedIsTrue : blockMapDefined ≡ true
    smallLargeFieldSplitDefinedIsTrue : smallLargeFieldSplitDefined ≡ true
    remainderDecayControlled : Bool
    gaugeFixingCompatible : Bool
    continuumStable : Bool
    remainderDecayControlledIsTrue : remainderDecayControlled ≡ true
    gaugeFixingCompatibleIsFalse : gaugeFixingCompatible ≡ false
    continuumStableIsFalse : continuumStable ≡ false
    openObligations : List BalabanRGLaneObligation
    openObligationsAreCanonical :
      openObligations ≡ canonicalBalabanRGLaneObligations
    noClayPromotion : clayYangMillsPromoted ≡ false

canonicalBalabanRGLane : BalabanRGLane
canonicalBalabanRGLane = record
  { receiptSurface = canonicalBalabanRGMassGapReceiptSurface
  ; stepVState = currentBalabanRGLaneState
  ; gaugeFixingGate = currentGaugeFixingCompatibilityGate
  ; continuumGate = currentContinuumStabilityGate
  ; blockSizeDefined = true
  ; effectiveActionDefined = true
  ; blockMapDefined = true
  ; smallLargeFieldSplitDefined = true
  ; blockSizeDefinedIsTrue = refl
  ; effectiveActionDefinedIsTrue = refl
  ; blockMapDefinedIsTrue = refl
  ; smallLargeFieldSplitDefinedIsTrue = refl
  ; remainderDecayControlled = true
  ; gaugeFixingCompatible = false
  ; continuumStable = false
  ; remainderDecayControlledIsTrue = refl
  ; gaugeFixingCompatibleIsFalse = refl
  ; continuumStableIsFalse = refl
  ; openObligations = canonicalBalabanRGLaneObligations
  ; openObligationsAreCanonical = refl
  ; noClayPromotion = refl
  }
