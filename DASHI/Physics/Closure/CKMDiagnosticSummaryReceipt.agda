module DASHI.Physics.Closure.CKMDiagnosticSummaryReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.AnomalyCancellationTableReceipt as Anomaly
import DASHI.Physics.Closure.CKMFullMatrixFromCarrierReceipt as Full
import DASHI.Physics.Closure.VubFromCarrierReceipt as Vub
import DASHI.Physics.Closure.YukawaNormalisationStructureReceipt as Norm

------------------------------------------------------------------------
-- CKM diagnostic summary receipt.
--
-- This packages the tranche diagnostics and keeps the terminal physical CKM
-- flag fail-closed.

data CKMDiagnosticSummaryStatus : Set where
  ckmDiagnosticTrancheSummarisedNoPromotion :
    CKMDiagnosticSummaryStatus

data CKMDiagnosticSummaryBlocker : Set where
  yukawaNormalisationPhysicalAuthorityMissing :
    CKMDiagnosticSummaryBlocker

  ckmDeg12RouteInconsistent :
    CKMDiagnosticSummaryBlocker

  naiveVubT5RouteFails :
    CKMDiagnosticSummaryBlocker

  carrierSMHyperchargeMatchMissing :
    CKMDiagnosticSummaryBlocker

canonicalCKMDiagnosticSummaryBlockers :
  List CKMDiagnosticSummaryBlocker
canonicalCKMDiagnosticSummaryBlockers =
  yukawaNormalisationPhysicalAuthorityMissing
  ∷ ckmDeg12RouteInconsistent
  ∷ naiveVubT5RouteFails
  ∷ carrierSMHyperchargeMatchMissing
  ∷ []

data CKMDiagnosticSummaryPromotion : Set where

ckmDiagnosticSummaryPromotionImpossibleHere :
  CKMDiagnosticSummaryPromotion →
  ⊥
ckmDiagnosticSummaryPromotionImpossibleHere ()

record CKMDiagnosticSummaryReceipt : Setω where
  field
    status :
      CKMDiagnosticSummaryStatus

    normalisationReceipt :
      Norm.YukawaNormalisationStructureReceipt

    normalisationReceiptIsCanonical :
      normalisationReceipt
      ≡
      Norm.canonicalYukawaNormalisationStructureReceipt

    fullMatrixReceipt :
      Full.CKMFullMatrixFromCarrierReceipt

    fullMatrixReceiptIsCanonical :
      fullMatrixReceipt ≡ Full.canonicalCKMFullMatrixFromCarrierReceipt

    anomalyReceipt :
      Anomaly.AnomalyCancellationTableReceipt

    anomalyReceiptKeepsCKMFalse :
      Bool

    anomalyReceiptKeepsCKMFalseIsTrue :
      anomalyReceiptKeepsCKMFalse ≡ true

    vubReceipt :
      Vub.VubFromCarrierReceipt

    vubReceiptIsCanonical :
      vubReceipt ≡ Vub.canonicalVubFromCarrierReceipt

    lambdaDirectFormulaRecorded :
      Bool

    lambdaDirectFormulaRecordedIsTrue :
      lambdaDirectFormulaRecorded ≡ true

    deg12NonIntegerInconsistencyRecorded :
      Bool

    deg12NonIntegerInconsistencyRecordedIsTrue :
      deg12NonIntegerInconsistencyRecorded ≡ true

    vubNaiveT5FailureRecorded :
      Bool

    vubNaiveT5FailureRecordedIsTrue :
      vubNaiveT5FailureRecorded ≡ true

    anomalyCancellationInheritedConditionally :
      Bool

    anomalyCancellationInheritedConditionallyIsTrue :
      anomalyCancellationInheritedConditionally ≡ true

    trancheSummary :
      List String

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    blockers :
      List CKMDiagnosticSummaryBlocker

    blockersAreCanonical :
      blockers ≡ canonicalCKMDiagnosticSummaryBlockers

    promotionFlags :
      List CKMDiagnosticSummaryPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open CKMDiagnosticSummaryReceipt public

canonicalCKMDiagnosticSummaryReceipt :
  CKMDiagnosticSummaryReceipt
canonicalCKMDiagnosticSummaryReceipt =
  record
    { status =
        ckmDiagnosticTrancheSummarisedNoPromotion
    ; normalisationReceipt =
        Norm.canonicalYukawaNormalisationStructureReceipt
    ; normalisationReceiptIsCanonical =
        refl
    ; fullMatrixReceipt =
        Full.canonicalCKMFullMatrixFromCarrierReceipt
    ; fullMatrixReceiptIsCanonical =
        refl
    ; anomalyReceipt =
        Anomaly.canonicalAnomalyCancellationTableReceipt
    ; anomalyReceiptKeepsCKMFalse =
        true
    ; anomalyReceiptKeepsCKMFalseIsTrue =
        refl
    ; vubReceipt =
        Vub.canonicalVubFromCarrierReceipt
    ; vubReceiptIsCanonical =
        refl
    ; lambdaDirectFormulaRecorded =
        true
    ; lambdaDirectFormulaRecordedIsTrue =
        refl
    ; deg12NonIntegerInconsistencyRecorded =
        true
    ; deg12NonIntegerInconsistencyRecordedIsTrue =
        refl
    ; vubNaiveT5FailureRecorded =
        true
    ; vubNaiveT5FailureRecordedIsTrue =
        refl
    ; anomalyCancellationInheritedConditionally =
        true
    ; anomalyCancellationInheritedConditionallyIsTrue =
        refl
    ; trancheSummary =
        "Yukawa normalisation is vol(X0(Nk))/sqrt(psi(Ni)*psi(Nj)); sqrt24=sqrt(6*4)"
        ∷ "CKM lambda uses the direct alpha1*pi*sqrt(3) formula; the degree-12 route has a non-integer inconsistency"
        ∷ "Naive degree-13 T5 |Vub| gives 0.02467 versus PDG 0.00369, about 569 percent high"
        ∷ "Anomaly cancellation is verified on the SM signed-sixth table inherited from the p3 Z/6 candidate"
        ∷ []
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; blockers =
        canonicalCKMDiagnosticSummaryBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "This receipt summarises the CKM/anomaly tranche diagnostics"
        ∷ "Each component receipt remains diagnostic or conditional"
        ∷ "The tranche does not promote physical CKM"
        ∷ []
    }

ckmDiagnosticSummaryDoesNotPromoteCKM :
  physicalCKMPromoted canonicalCKMDiagnosticSummaryReceipt ≡ false
ckmDiagnosticSummaryDoesNotPromoteCKM =
  refl
