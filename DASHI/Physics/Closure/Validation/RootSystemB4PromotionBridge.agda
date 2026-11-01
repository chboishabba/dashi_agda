module DASHI.Physics.Closure.Validation.RootSystemB4PromotionBridge where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Geometry.ConeTimeIsotropy as CTI

open import DASHI.Physics.Closure.Validation.RootSystemB4ShellComparison as B4C
open import DASHI.Physics.Closure.Validation.RootSystemB4OrientationSignatureBridge as B4OSB

data B4OrientationStatus : Set where
  orientationJustified : B4OrientationStatus

data B4SignatureStatus : Set where
  signatureJustified : B4SignatureStatus

data B4PromotionBridgeStatus : Set where
  admissiblePromotionReady : B4PromotionBridgeStatus

record B4PromotionBridge : Set where
  field
    shell1Matches : Bool
    shell2Matches : Bool
    orientationStatus : B4OrientationStatus
    signatureStatus : B4SignatureStatus
    orientationTag : Nat
    signature : CTI.Signature
    promotionStatus : B4PromotionBridgeStatus

bridge : B4PromotionBridge
bridge =
  record
    { shell1Matches = B4C.B4ShellComparisonReport.shell1Matches B4C.report
    ; shell2Matches = B4C.B4ShellComparisonReport.shell2Matches B4C.report
    ; orientationStatus = orientationJustified
    ; signatureStatus = signatureJustified
    ; orientationTag = B4OSB.b4OrientationTag
    ; signature = B4OSB.b4Signature
    ; promotionStatus = admissiblePromotionReady
    }
