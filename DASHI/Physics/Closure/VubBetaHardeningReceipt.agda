module DASHI.Physics.Closure.VubBetaHardeningReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Manager C4: Vub/beta CKM hardening receipt.
--
-- This receipt records the C4 hardening step only.  It upgrades the status
-- of the Vub and beta carrier receipts for Paper 6 readiness while keeping
-- the physical CKM promotion gate closed.

data CKMPaperSixReadiness : Set where
  upgraded :
    CKMPaperSixReadiness

data VubHardeningUpgrade : Set where
  upgradedFromFNTextureToCarrierArithmetic :
    VubHardeningUpgrade

data VubHardeningDerivation : Set where
  adjacentOnlyChainDerivation :
    VubHardeningDerivation

data BetaHardeningUpgrade : Set where
  upgradedFromDownstreamReconstructionToIndependentDualStructure :
    BetaHardeningUpgrade

data BetaHardeningDerivation : Set where
  independentDualStructureDerivation :
    BetaHardeningDerivation

data CKMHardeningCorrectionStatus : Set where
  higherOrderCKMUnitarityCorrectionsExpectedOpen :
    CKMHardeningCorrectionStatus

data UpstreamCKMReceiptReference : Set where
  vubAlpha12ProductReceipt :
    UpstreamCKMReceiptReference

  betaAngleFromCarrierReceipt :
    UpstreamCKMReceiptReference

data VubBetaHardeningBlocker : Set where
  physicalCKMPromotionStillFalse :
    VubBetaHardeningBlocker

  higherOrderCKMUnitarityCorrectionsOpen :
    VubBetaHardeningBlocker

  fullPhysicalCKMDiagonalisationAuthorityMissing :
    VubBetaHardeningBlocker

canonicalVubBetaHardeningBlockers :
  List VubBetaHardeningBlocker
canonicalVubBetaHardeningBlockers =
  physicalCKMPromotionStillFalse
  ∷ higherOrderCKMUnitarityCorrectionsOpen
  ∷ fullPhysicalCKMDiagonalisationAuthorityMissing
  ∷ []

data VubBetaHardeningPromotion : Set where

vubBetaHardeningPromotionImpossibleHere :
  VubBetaHardeningPromotion →
  ⊥
vubBetaHardeningPromotionImpossibleHere ()

vubHardeningStatement : String
vubHardeningStatement =
  "VubAlpha12ProductReceipt upgraded from FN texture to carrier arithmetic via adjacent-only chain derivation"

betaHardeningStatement : String
betaHardeningStatement =
  "BetaAngleFromCarrierReceipt upgraded from downstream reconstruction to independent dual-structure derivation"

ckmUnitarityCorrectionStatement : String
ckmUnitarityCorrectionStatement =
  "higher-order CKM unitarity corrections remain expected/open"

canonicalVubBetaHardeningBoundary :
  List String
canonicalVubBetaHardeningBoundary =
  "Manager C4 records CKM hardening for Vub and beta"
  ∷ vubHardeningStatement
  ∷ "Vub error remains recorded as 4.16 percent"
  ∷ betaHardeningStatement
  ∷ "Beta error remains recorded as 6 percent"
  ∷ ckmUnitarityCorrectionStatement
  ∷ "ckmPaperSixReadiness = upgraded"
  ∷ "Physical CKM promotion remains false"
  ∷ []

record VubBetaHardeningReceipt : Setω where
  field
    vubReceipt :
      UpstreamCKMReceiptReference

    betaReceipt :
      UpstreamCKMReceiptReference

    vubReceiptIsAlpha12Product :
      vubReceipt ≡ vubAlpha12ProductReceipt

    betaReceiptIsAngleFromCarrier :
      betaReceipt ≡ betaAngleFromCarrierReceipt

    ckmPaperSixReadiness :
      CKMPaperSixReadiness

    ckmPaperSixReadinessIsUpgraded :
      ckmPaperSixReadiness ≡ upgraded

    vubUpgrade :
      VubHardeningUpgrade

    vubUpgradeIsCarrierArithmetic :
      vubUpgrade ≡ upgradedFromFNTextureToCarrierArithmetic

    vubDerivation :
      VubHardeningDerivation

    vubDerivationIsAdjacentOnly :
      vubDerivation ≡ adjacentOnlyChainDerivation

    vubHardeningSummary :
      String

    vubHardeningSummaryIsCanonical :
      vubHardeningSummary ≡ vubHardeningStatement

    vubErrorPercent :
      Float

    vubErrorPercentIsFourPointSixteen :
      vubErrorPercent ≡ 4.16

    betaUpgrade :
      BetaHardeningUpgrade

    betaUpgradeIsIndependentDualStructure :
      betaUpgrade
      ≡
      upgradedFromDownstreamReconstructionToIndependentDualStructure

    betaDerivation :
      BetaHardeningDerivation

    betaDerivationIsIndependentDualStructure :
      betaDerivation ≡ independentDualStructureDerivation

    betaHardeningSummary :
      String

    betaHardeningSummaryIsCanonical :
      betaHardeningSummary ≡ betaHardeningStatement

    betaErrorPercent :
      Float

    betaErrorPercentIsSix :
      betaErrorPercent ≡ 6.0

    betaErrorRoundedFromReceipt :
      betaErrorPercent ≡ 6.0

    higherOrderCKMUnitarityCorrections :
      CKMHardeningCorrectionStatus

    higherOrderCKMUnitarityCorrectionsAreOpen :
      higherOrderCKMUnitarityCorrections
      ≡
      higherOrderCKMUnitarityCorrectionsExpectedOpen

    higherOrderCKMUnitarityCorrectionLabel :
      String

    higherOrderCKMUnitarityCorrectionLabelIsCanonical :
      higherOrderCKMUnitarityCorrectionLabel
      ≡
      ckmUnitarityCorrectionStatement

    physicalVubPromoted :
      Bool

    physicalVubPromotedIsFalse :
      physicalVubPromoted ≡ false

    physicalBetaPromoted :
      Bool

    physicalBetaPromotedIsFalse :
      physicalBetaPromoted ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    blockers :
      List VubBetaHardeningBlocker

    blockersAreCanonical :
      blockers ≡ canonicalVubBetaHardeningBlockers

    promotionFlags :
      List VubBetaHardeningPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ canonicalVubBetaHardeningBoundary

open VubBetaHardeningReceipt public

canonicalVubBetaHardeningReceipt :
  VubBetaHardeningReceipt
canonicalVubBetaHardeningReceipt =
  record
    { vubReceipt =
        vubAlpha12ProductReceipt
    ; betaReceipt =
        betaAngleFromCarrierReceipt
    ; vubReceiptIsAlpha12Product =
        refl
    ; betaReceiptIsAngleFromCarrier =
        refl
    ; ckmPaperSixReadiness =
        upgraded
    ; ckmPaperSixReadinessIsUpgraded =
        refl
    ; vubUpgrade =
        upgradedFromFNTextureToCarrierArithmetic
    ; vubUpgradeIsCarrierArithmetic =
        refl
    ; vubDerivation =
        adjacentOnlyChainDerivation
    ; vubDerivationIsAdjacentOnly =
        refl
    ; vubHardeningSummary =
        vubHardeningStatement
    ; vubHardeningSummaryIsCanonical =
        refl
    ; vubErrorPercent =
        4.16
    ; vubErrorPercentIsFourPointSixteen =
        refl
    ; betaUpgrade =
        upgradedFromDownstreamReconstructionToIndependentDualStructure
    ; betaUpgradeIsIndependentDualStructure =
        refl
    ; betaDerivation =
        independentDualStructureDerivation
    ; betaDerivationIsIndependentDualStructure =
        refl
    ; betaHardeningSummary =
        betaHardeningStatement
    ; betaHardeningSummaryIsCanonical =
        refl
    ; betaErrorPercent =
        6.0
    ; betaErrorPercentIsSix =
        refl
    ; betaErrorRoundedFromReceipt =
        refl
    ; higherOrderCKMUnitarityCorrections =
        higherOrderCKMUnitarityCorrectionsExpectedOpen
    ; higherOrderCKMUnitarityCorrectionsAreOpen =
        refl
    ; higherOrderCKMUnitarityCorrectionLabel =
        ckmUnitarityCorrectionStatement
    ; higherOrderCKMUnitarityCorrectionLabelIsCanonical =
        refl
    ; physicalVubPromoted =
        false
    ; physicalVubPromotedIsFalse =
        refl
    ; physicalBetaPromoted =
        false
    ; physicalBetaPromotedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; blockers =
        canonicalVubBetaHardeningBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        canonicalVubBetaHardeningBoundary
    ; receiptBoundaryIsCanonical =
        refl
    }

ckmPaperSixReadinessUpgraded :
  ckmPaperSixReadiness canonicalVubBetaHardeningReceipt ≡ upgraded
ckmPaperSixReadinessUpgraded =
  refl

vubHardeningUsesAdjacentOnlyCarrierArithmetic :
  vubDerivation canonicalVubBetaHardeningReceipt
  ≡
  adjacentOnlyChainDerivation
vubHardeningUsesAdjacentOnlyCarrierArithmetic =
  refl

betaHardeningUsesIndependentDualStructure :
  betaDerivation canonicalVubBetaHardeningReceipt
  ≡
  independentDualStructureDerivation
betaHardeningUsesIndependentDualStructure =
  refl

vubBetaHardeningKeepsPhysicalCKMFalse :
  physicalCKMPromoted canonicalVubBetaHardeningReceipt ≡ false
vubBetaHardeningKeepsPhysicalCKMFalse =
  refl

vubBetaHardeningNoPromotion :
  VubBetaHardeningPromotion →
  ⊥
vubBetaHardeningNoPromotion =
  vubBetaHardeningPromotionImpossibleHere
