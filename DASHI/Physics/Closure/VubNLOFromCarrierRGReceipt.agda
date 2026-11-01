module DASHI.Physics.Closure.VubNLOFromCarrierRGReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Vub NLO from carrier RG audit receipt.
--
-- This receipt audits whether the degree-28 Vub NLO QCD correction can be
-- derived from the carrier RG.  It records the Planck-to-m_b depth estimate
-- and the key obstruction: the carrier alpha1 bookkeeping parameter is not
-- the QCD strong coupling alpha_s.  Therefore an NLO correction requires a
-- separate QCD running calculation and is not promoted here.

data VubNLOFromCarrierRGStatus : Set where
  carrierRGNLOQCDRouteAuditedDerivationBlocked :
    VubNLOFromCarrierRGStatus

data VubNLOFromCarrierRGBlocker : Set where
  carrierAlphaOneIsNotQCDAlphaS :
    VubNLOFromCarrierRGBlocker

  missingQCDRunningAuthority :
    VubNLOFromCarrierRGBlocker

  missingThresholdMatchedAlphaSAtMB :
    VubNLOFromCarrierRGBlocker

  missingDegreeTwentyEightNLODerivation :
    VubNLOFromCarrierRGBlocker

  missingPhysicalVubAuthority :
    VubNLOFromCarrierRGBlocker

canonicalVubNLOFromCarrierRGBlockers :
  List VubNLOFromCarrierRGBlocker
canonicalVubNLOFromCarrierRGBlockers =
  carrierAlphaOneIsNotQCDAlphaS
  ∷ missingQCDRunningAuthority
  ∷ missingThresholdMatchedAlphaSAtMB
  ∷ missingDegreeTwentyEightNLODerivation
  ∷ missingPhysicalVubAuthority
  ∷ []

data VubNLOFromCarrierRGPromotion : Set where

vubNLOFromCarrierRGPromotionImpossibleHere :
  VubNLOFromCarrierRGPromotion →
  ⊥
vubNLOFromCarrierRGPromotionImpossibleHere ()

degreeTwentyEightVubNLOLabel : String
degreeTwentyEightVubNLOLabel =
  "degree-28 Vub NLO QCD correction audit"

planckToMBDepthLabel : String
planckToMBDepthLabel =
  "Planck-to-m_b carrier depth estimate is approximately 13.3"

alphaOneLabel : String
alphaOneLabel =
  "carrier alpha1 is the DASHI/Yukawa bookkeeping parameter, approximately 0.04124"

alphaSLabel : String
alphaSLabel =
  "QCD alpha_s is the threshold-matched strong coupling; it is not identified with carrier alpha1"

nloRequiresQCDRunningLabel : String
nloRequiresQCDRunningLabel =
  "NLO QCD correction requires separate QCD running and threshold matching, not carrier RG alone"

auditConclusionLabel : String
auditConclusionLabel =
  "carrier alpha1 is not QCD alpha_s; degree-28 Vub NLO correction is not derived from carrier RG"

record VubNLOFromCarrierRGReceipt : Set where
  field
    status :
      VubNLOFromCarrierRGStatus

    auditTarget :
      String

    auditTargetIsCanonical :
      auditTarget ≡ degreeTwentyEightVubNLOLabel

    degreeVubNLO :
      Nat

    degreeVubNLOIsTwentyEight :
      degreeVubNLO ≡ 28

    planckToMBDepthEstimate :
      Float

    planckToMBDepthStatement :
      String

    planckToMBDepthStatementIsCanonical :
      planckToMBDepthStatement ≡ planckToMBDepthLabel

    carrierAlphaOneStatement :
      String

    carrierAlphaOneStatementIsCanonical :
      carrierAlphaOneStatement ≡ alphaOneLabel

    qcdAlphaSStatement :
      String

    qcdAlphaSStatementIsCanonical :
      qcdAlphaSStatement ≡ alphaSLabel

    alphaOneIdentifiedWithAlphaS :
      Bool

    alphaOneIdentifiedWithAlphaSIsFalse :
      alphaOneIdentifiedWithAlphaS ≡ false

    carrierRGDepthRecorded :
      Bool

    carrierRGDepthRecordedIsTrue :
      carrierRGDepthRecorded ≡ true

    nloQCDCorrectionRequiresSeparateRunning :
      Bool

    nloQCDCorrectionRequiresSeparateRunningIsTrue :
      nloQCDCorrectionRequiresSeparateRunning ≡ true

    nloQCDRunningStatement :
      String

    nloQCDRunningStatementIsCanonical :
      nloQCDRunningStatement ≡ nloRequiresQCDRunningLabel

    degreeTwentyEightCorrectionDerivedFromCarrierRG :
      Bool

    degreeTwentyEightCorrectionDerivedFromCarrierRGIsFalse :
      degreeTwentyEightCorrectionDerivedFromCarrierRG ≡ false

    auditConclusion :
      String

    auditConclusionIsCanonical :
      auditConclusion ≡ auditConclusionLabel

    physicalVubPromoted :
      Bool

    physicalVubPromotedIsFalse :
      physicalVubPromoted ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    blockers :
      List VubNLOFromCarrierRGBlocker

    blockersAreCanonical :
      blockers ≡ canonicalVubNLOFromCarrierRGBlockers

    promotionFlags :
      List VubNLOFromCarrierRGPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open VubNLOFromCarrierRGReceipt public

canonicalVubNLOFromCarrierRGReceipt :
  VubNLOFromCarrierRGReceipt
canonicalVubNLOFromCarrierRGReceipt =
  record
    { status =
        carrierRGNLOQCDRouteAuditedDerivationBlocked
    ; auditTarget =
        degreeTwentyEightVubNLOLabel
    ; auditTargetIsCanonical =
        refl
    ; degreeVubNLO =
        28
    ; degreeVubNLOIsTwentyEight =
        refl
    ; planckToMBDepthEstimate =
        13.3
    ; planckToMBDepthStatement =
        planckToMBDepthLabel
    ; planckToMBDepthStatementIsCanonical =
        refl
    ; carrierAlphaOneStatement =
        alphaOneLabel
    ; carrierAlphaOneStatementIsCanonical =
        refl
    ; qcdAlphaSStatement =
        alphaSLabel
    ; qcdAlphaSStatementIsCanonical =
        refl
    ; alphaOneIdentifiedWithAlphaS =
        false
    ; alphaOneIdentifiedWithAlphaSIsFalse =
        refl
    ; carrierRGDepthRecorded =
        true
    ; carrierRGDepthRecordedIsTrue =
        refl
    ; nloQCDCorrectionRequiresSeparateRunning =
        true
    ; nloQCDCorrectionRequiresSeparateRunningIsTrue =
        refl
    ; nloQCDRunningStatement =
        nloRequiresQCDRunningLabel
    ; nloQCDRunningStatementIsCanonical =
        refl
    ; degreeTwentyEightCorrectionDerivedFromCarrierRG =
        false
    ; degreeTwentyEightCorrectionDerivedFromCarrierRGIsFalse =
        refl
    ; auditConclusion =
        auditConclusionLabel
    ; auditConclusionIsCanonical =
        refl
    ; physicalVubPromoted =
        false
    ; physicalVubPromotedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; blockers =
        canonicalVubNLOFromCarrierRGBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The degree-28 Vub NLO QCD correction route was audited against carrier RG"
        ∷ "The Planck-to-m_b carrier depth estimate is recorded as approximately 13.3"
        ∷ "Carrier alpha1 is not identified with QCD alpha_s"
        ∷ "A genuine NLO correction requires separate QCD running and threshold matching"
        ∷ "degreeTwentyEightCorrectionDerivedFromCarrierRG remains false"
        ∷ "physicalVubPromoted remains false"
        ∷ "physicalCKMPromoted remains false"
        ∷ []
    }

vubNLOCarrierRGRecordsDepth :
  carrierRGDepthRecorded canonicalVubNLOFromCarrierRGReceipt ≡ true
vubNLOCarrierRGRecordsDepth =
  refl

vubNLOCarrierRGDoesNotIdentifyAlphaOneWithAlphaS :
  alphaOneIdentifiedWithAlphaS canonicalVubNLOFromCarrierRGReceipt ≡ false
vubNLOCarrierRGDoesNotIdentifyAlphaOneWithAlphaS =
  refl

vubNLOCarrierRGKeepsCorrectionUndderived :
  degreeTwentyEightCorrectionDerivedFromCarrierRG
    canonicalVubNLOFromCarrierRGReceipt
  ≡
  false
vubNLOCarrierRGKeepsCorrectionUndderived =
  refl

vubNLOCarrierRGDoesNotPromoteVub :
  physicalVubPromoted canonicalVubNLOFromCarrierRGReceipt ≡ false
vubNLOCarrierRGDoesNotPromoteVub =
  refl

vubNLOCarrierRGDoesNotPromoteCKM :
  physicalCKMPromoted canonicalVubNLOFromCarrierRGReceipt ≡ false
vubNLOCarrierRGDoesNotPromoteCKM =
  refl
