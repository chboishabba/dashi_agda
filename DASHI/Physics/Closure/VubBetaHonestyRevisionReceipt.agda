module DASHI.Physics.Closure.VubBetaHonestyRevisionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Manager C1: Vub/beta honesty revision receipt.
--
-- This receipt corrects the earlier VubBetaHardeningReceipt without
-- importing it.  The alpha1*alpha2 readback is retained only as a
-- leading-order diagonal/down-identity approximation.  The full
-- next-order down-type mixing readback is recorded as failing.

data VubBetaHonestyRevisionStatus : Set where
  priorHardeningCorrectedFailClosed :
    VubBetaHonestyRevisionStatus

data VubAlpha12Scope : Set where
  validOnlyInUpDiagonalDownIdentityApproximation :
    VubAlpha12Scope

data FullDownMixingCheck : Set where
  fullNextOrderDownTypeMixingFails :
    FullDownMixingCheck

data AdjacentOnlyOriginStatus : Set where
  structuralChainOriginRemainsValid :
    AdjacentOnlyOriginStatus

data CarrierLabelDiscipline : Set where
  carrierDerivedLabelsMustBeQualified :
    CarrierLabelDiscipline

data VubBetaHonestyBlocker : Set where
  alpha12NotFullPhysicalVub :
    VubBetaHonestyBlocker

  fullNextOrderDownTypeMixingFailure :
    VubBetaHonestyBlocker

  carrierDerivedLabelRequiresQualification :
    VubBetaHonestyBlocker

  physicalCKMAuthorityStillMissing :
    VubBetaHonestyBlocker

canonicalVubBetaHonestyBlockers :
  List VubBetaHonestyBlocker
canonicalVubBetaHonestyBlockers =
  alpha12NotFullPhysicalVub
  ∷ fullNextOrderDownTypeMixingFailure
  ∷ carrierDerivedLabelRequiresQualification
  ∷ physicalCKMAuthorityStillMissing
  ∷ []

data VubBetaHonestyPromotion : Set where

vubBetaHonestyPromotionImpossibleHere :
  VubBetaHonestyPromotion →
  ⊥
vubBetaHonestyPromotionImpossibleHere ()

alpha12QualifiedFormulaLabel : String
alpha12QualifiedFormulaLabel =
  "|Vub| approx alpha1*alpha2 only in the U_d approximately identity / diagonal approximation"

fullMixingFailureLabel : String
fullMixingFailureLabel =
  "full next-order down-type mixing fails for the alpha1*alpha2 physical-Vub readback"

adjacentOnlyOriginLabel : String
adjacentOnlyOriginLabel =
  "adjacent-only carrier chain origin remains valid as a structural origin for the up-type 1-3 entry"

carrierLabelQualificationLabel : String
carrierLabelQualificationLabel =
  "carrier-derived labels must be qualified as approximation/candidate labels unless physical CKM authority is supplied"

canonicalVubBetaHonestyBoundary :
  List String
canonicalVubBetaHonestyBoundary =
  "Manager C1 corrects the prior VubBetaHardeningReceipt fail-closed"
  ∷ alpha12QualifiedFormulaLabel
  ∷ fullMixingFailureLabel
  ∷ adjacentOnlyOriginLabel
  ∷ "The 4.2 percent leading-order numerical accuracy remains recorded"
  ∷ carrierLabelQualificationLabel
  ∷ "No physical Vub, beta, CKM, Paper 6, Clay, or terminal promotion is issued"
  ∷ []

record VubBetaHonestyRevisionReceipt : Setω where
  field
    status :
      VubBetaHonestyRevisionStatus

    statusIsCorrection :
      status ≡ priorHardeningCorrectedFailClosed

    correctsPriorReceipt :
      String

    correctsPriorReceiptIsCanonical :
      correctsPriorReceipt ≡ "VubBetaHardeningReceipt"

    alpha12Scope :
      VubAlpha12Scope

    alpha12ScopeIsDiagonalApproximationOnly :
      alpha12Scope ≡ validOnlyInUpDiagonalDownIdentityApproximation

    alpha12QualifiedFormula :
      String

    alpha12QualifiedFormulaIsCanonical :
      alpha12QualifiedFormula ≡ alpha12QualifiedFormulaLabel

    udApproximatelyIdentityDiagonalApproximation :
      Bool

    udApproximatelyIdentityDiagonalApproximationIsTrue :
      udApproximatelyIdentityDiagonalApproximation ≡ true

    alpha12ValidAsFullNextOrderPhysicalVub :
      Bool

    alpha12ValidAsFullNextOrderPhysicalVubIsFalse :
      alpha12ValidAsFullNextOrderPhysicalVub ≡ false

    fullDownMixingCheck :
      FullDownMixingCheck

    fullDownMixingCheckFails :
      fullDownMixingCheck ≡ fullNextOrderDownTypeMixingFails

    fullDownMixingFailureSummary :
      String

    fullDownMixingFailureSummaryIsCanonical :
      fullDownMixingFailureSummary ≡ fullMixingFailureLabel

    adjacentOnlyOriginStatus :
      AdjacentOnlyOriginStatus

    adjacentOnlyOriginStatusIsValid :
      adjacentOnlyOriginStatus ≡ structuralChainOriginRemainsValid

    adjacentOnlyOriginSummary :
      String

    adjacentOnlyOriginSummaryIsCanonical :
      adjacentOnlyOriginSummary ≡ adjacentOnlyOriginLabel

    leadingOrderAccuracyPercent :
      Float

    leadingOrderAccuracyPercentIsFourPointTwo :
      leadingOrderAccuracyPercent ≡ 4.2

    leadingOrderAccuracyRemainsValid :
      Bool

    leadingOrderAccuracyRemainsValidIsTrue :
      leadingOrderAccuracyRemainsValid ≡ true

    carrierLabelDiscipline :
      CarrierLabelDiscipline

    carrierLabelDisciplineIsQualified :
      carrierLabelDiscipline ≡ carrierDerivedLabelsMustBeQualified

    carrierLabelQualification :
      String

    carrierLabelQualificationIsCanonical :
      carrierLabelQualification ≡ carrierLabelQualificationLabel

    carrierDerivedUnqualifiedLabelPromoted :
      Bool

    carrierDerivedUnqualifiedLabelPromotedIsFalse :
      carrierDerivedUnqualifiedLabelPromoted ≡ false

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

    paperSixReadinessPromoted :
      Bool

    paperSixReadinessPromotedIsFalse :
      paperSixReadinessPromoted ≡ false

    clayPromotionGate :
      Bool

    clayPromotionGateIsFalse :
      clayPromotionGate ≡ false

    terminalPromotionGate :
      Bool

    terminalPromotionGateIsFalse :
      terminalPromotionGate ≡ false

    blockers :
      List VubBetaHonestyBlocker

    blockersAreCanonical :
      blockers ≡ canonicalVubBetaHonestyBlockers

    promotionFlags :
      List VubBetaHonestyPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ canonicalVubBetaHonestyBoundary

open VubBetaHonestyRevisionReceipt public

canonicalVubBetaHonestyRevisionReceipt :
  VubBetaHonestyRevisionReceipt
canonicalVubBetaHonestyRevisionReceipt =
  record
    { status =
        priorHardeningCorrectedFailClosed
    ; statusIsCorrection =
        refl
    ; correctsPriorReceipt =
        "VubBetaHardeningReceipt"
    ; correctsPriorReceiptIsCanonical =
        refl
    ; alpha12Scope =
        validOnlyInUpDiagonalDownIdentityApproximation
    ; alpha12ScopeIsDiagonalApproximationOnly =
        refl
    ; alpha12QualifiedFormula =
        alpha12QualifiedFormulaLabel
    ; alpha12QualifiedFormulaIsCanonical =
        refl
    ; udApproximatelyIdentityDiagonalApproximation =
        true
    ; udApproximatelyIdentityDiagonalApproximationIsTrue =
        refl
    ; alpha12ValidAsFullNextOrderPhysicalVub =
        false
    ; alpha12ValidAsFullNextOrderPhysicalVubIsFalse =
        refl
    ; fullDownMixingCheck =
        fullNextOrderDownTypeMixingFails
    ; fullDownMixingCheckFails =
        refl
    ; fullDownMixingFailureSummary =
        fullMixingFailureLabel
    ; fullDownMixingFailureSummaryIsCanonical =
        refl
    ; adjacentOnlyOriginStatus =
        structuralChainOriginRemainsValid
    ; adjacentOnlyOriginStatusIsValid =
        refl
    ; adjacentOnlyOriginSummary =
        adjacentOnlyOriginLabel
    ; adjacentOnlyOriginSummaryIsCanonical =
        refl
    ; leadingOrderAccuracyPercent =
        4.2
    ; leadingOrderAccuracyPercentIsFourPointTwo =
        refl
    ; leadingOrderAccuracyRemainsValid =
        true
    ; leadingOrderAccuracyRemainsValidIsTrue =
        refl
    ; carrierLabelDiscipline =
        carrierDerivedLabelsMustBeQualified
    ; carrierLabelDisciplineIsQualified =
        refl
    ; carrierLabelQualification =
        carrierLabelQualificationLabel
    ; carrierLabelQualificationIsCanonical =
        refl
    ; carrierDerivedUnqualifiedLabelPromoted =
        false
    ; carrierDerivedUnqualifiedLabelPromotedIsFalse =
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
    ; paperSixReadinessPromoted =
        false
    ; paperSixReadinessPromotedIsFalse =
        refl
    ; clayPromotionGate =
        false
    ; clayPromotionGateIsFalse =
        refl
    ; terminalPromotionGate =
        false
    ; terminalPromotionGateIsFalse =
        refl
    ; blockers =
        canonicalVubBetaHonestyBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        canonicalVubBetaHonestyBoundary
    ; receiptBoundaryIsCanonical =
        refl
    }

vubAlpha12ScopeIsApproximationOnly :
  alpha12Scope canonicalVubBetaHonestyRevisionReceipt
  ≡
  validOnlyInUpDiagonalDownIdentityApproximation
vubAlpha12ScopeIsApproximationOnly =
  refl

vubFullNextOrderDownMixingFails :
  fullDownMixingCheck canonicalVubBetaHonestyRevisionReceipt
  ≡
  fullNextOrderDownTypeMixingFails
vubFullNextOrderDownMixingFails =
  refl

vubAdjacentOnlyOriginStillValid :
  adjacentOnlyOriginStatus canonicalVubBetaHonestyRevisionReceipt
  ≡
  structuralChainOriginRemainsValid
vubAdjacentOnlyOriginStillValid =
  refl

vubLeadingOrderAccuracyStillValid :
  leadingOrderAccuracyRemainsValid canonicalVubBetaHonestyRevisionReceipt
  ≡
  true
vubLeadingOrderAccuracyStillValid =
  refl

vubBetaHonestyPromotionGatesFalse :
  physicalVubPromoted canonicalVubBetaHonestyRevisionReceipt
  ≡
  false
vubBetaHonestyPromotionGatesFalse =
  refl

vubBetaHonestyNoPromotion :
  VubBetaHonestyPromotion →
  ⊥
vubBetaHonestyNoPromotion =
  vubBetaHonestyPromotionImpossibleHere
