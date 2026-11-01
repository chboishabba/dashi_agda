module DASHI.Physics.Closure.Validation.SyntheticOneMinusPromotionBridge where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Geometry.ConeTimeIsotropy as CTI

open import DASHI.Physics.Closure.Validation.SyntheticOneMinusShellComparison as SOSC
open import DASHI.Physics.Closure.Validation.SyntheticOneMinusOrientationSignatureBridge as SOSB
open import DASHI.Physics.LorentzNeighborhoodDynamicCandidate as LNDC

data SyntheticOrientationStatus : Set where
  orientationBlocked : SyntheticOrientationStatus
  orientationJustified : SyntheticOrientationStatus

data SyntheticSignatureStatus : Set where
  signatureBlocked : SyntheticSignatureStatus
  signatureJustified : SyntheticSignatureStatus

data SyntheticPromotionBridgeStatus : Set where
  blockedOnOrientationAndSignature : SyntheticPromotionBridgeStatus
  blockedOnDynamicsOnly : SyntheticPromotionBridgeStatus
  blockedOnSignatureOnly : SyntheticPromotionBridgeStatus
  admissiblePromotionReady : SyntheticPromotionBridgeStatus

record SyntheticPromotionBridge : Set where
  field
    shell1Matches : Bool
    shell2Matches : Bool
    orientationStatus : SyntheticOrientationStatus
    signatureStatus : SyntheticSignatureStatus
    orientationTag : Nat
    signature : CTI.Signature
    promotionStatus : SyntheticPromotionBridgeStatus

bridge : SyntheticPromotionBridge
bridge =
  record
    { shell1Matches = SOSC.SyntheticShellComparisonReport.shell1Matches SOSC.report
    ; shell2Matches = SOSC.SyntheticShellComparisonReport.shell2Matches SOSC.report
    ; orientationStatus = orientationJustified
    ; signatureStatus = signatureJustified
    ; orientationTag = SOSB.syntheticOrientationTag
    ; signature = SOSB.syntheticSignature
    ; promotionStatus = admissiblePromotionReady
    }
