module DASHI.Physics.Thermodynamics.MagnothermAttributionValidation where

open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.GenericReceipt as Receipt
import DASHI.Physics.Thermodynamics.MagnothermAttributedEvidenceExact as Evidence

-- Attribution firewall regression surface.  This file is intentionally small:
-- it checks the canonical source atlas is non-promoting and that the acquired
-- observation / vendor / future-work classes stay definitionally distinct.

sourceAtlasDoesNotPromote :
  Receipt.promotesClaim Evidence.magnothermAttributedSourceReceipt ≡ false
sourceAtlasDoesNotPromote = refl

peerReviewedObservationIsNotVendorClaim :
  Evidence.peerReviewedObservation ≡ Evidence.vendorTechnologyClaim → ⊥
peerReviewedObservationIsNotVendorClaim ()

vendorTechnologyIsNotDevelopmentVision :
  Evidence.vendorTechnologyClaim ≡ Evidence.vendorDevelopmentVision → ⊥
vendorTechnologyIsNotDevelopmentVision ()

plannedFutureWorkIsNotCompletedObservation :
  Evidence.plannedFutureExperiment ≡ Evidence.peerReviewedObservation → ⊥
plannedFutureWorkIsNotCompletedObservation ()

sixWeekEvidenceIsPrimaryForItsBoundedClaim :
  Evidence.ClaimPayment.primaryForClaim Evidence.sixWeekContinuedOperationPayment ≡ true
sixWeekEvidenceIsPrimaryForItsBoundedClaim = refl

threeMonthEvidenceIsPreliminary :
  Evidence.ClaimPayment.preliminary Evidence.threeMonthMicrochannelPayment ≡ true
threeMonthEvidenceIsPreliminary = refl

longTermPlanIsNotEmpiricalPayment :
  Evidence.ClaimPayment.empiricalPayment Evidence.longTermExperimentPlanPayment ≡ false
longTermPlanIsNotEmpiricalPayment = refl

vendorThirtyPercentIsNotCalibration :
  Evidence.ClaimPayment.calibratedDeviceEvidence Evidence.vendorThirtyPercentWorkRecoveryPayment ≡ false
vendorThirtyPercentIsNotCalibration = refl

stellarFiveTeslaIsTargetNotMeasurement :
  Evidence.ClaimPayment.empiricalPayment Evidence.stellarFiveTeslaTargetPayment ≡ false
stellarFiveTeslaIsTargetNotMeasurement = refl
