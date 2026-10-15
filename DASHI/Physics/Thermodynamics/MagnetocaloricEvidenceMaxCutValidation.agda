module DASHI.Physics.Thermodynamics.MagnetocaloricEvidenceMaxCutValidation where

open import DASHI.Core.Prelude
import DASHI.Physics.Thermodynamics.MagnetocaloricEvidenceMaxCutExact as MaxCut

sixWeekAgingPaid :
  MaxCut.PaymentRow.status MaxCut.sixWeekAgingRow ≡ MaxCut.peerReviewedPaid
sixWeekAgingPaid = refl

threeMonthStillPreliminary :
  MaxCut.PaymentRow.qualifier MaxCut.threeMonthMicrochannelRow
  ≡ MaxCut.preliminaryOnly
threeMonthStillPreliminary = refl

oneTeslaFunctionCheckPaid :
  MaxCut.PaymentRow.status MaxCut.oneTeslaAdiabaticCharacterizationRow
  ≡ MaxCut.peerReviewedPaid
oneTeslaFunctionCheckPaid = refl

agingOperatingPointIsPartial :
  MaxCut.PaymentRow.status MaxCut.agingTestOperatingPointRow
  ≡ MaxCut.peerReviewedPartial
agingOperatingPointIsPartial = refl

agingOperatingPointDoesNotCloseFieldMap :
  MaxCut.PaymentRow.status MaxCut.fieldMapRow ≡ MaxCut.structurallyTyped
agingOperatingPointDoesNotCloseFieldMap = refl

agingOperatingPointDoesNotCloseCycleControl :
  MaxCut.PaymentRow.status MaxCut.cycleTimingRow ≡ MaxCut.structurallyTyped
agingOperatingPointDoesNotCloseCycleControl = refl

longTermLifetimeOpen :
  MaxCut.PaymentRow.status MaxCut.longTermLifetimeRow ≡ MaxCut.openSameObjectAcquisition
longTermLifetimeOpen = refl

vendorEfficiencyNotCalibration :
  MaxCut.PaymentRow.status MaxCut.vendorThirtyPercentRow ≡ MaxCut.vendorSourceOnly
vendorEfficiencyNotCalibration = refl

stellarFieldNotMeasuredDevice :
  MaxCut.PaymentRow.status MaxCut.stellarFiveTeslaRow ≡ MaxCut.vendorSourceOnly
stellarFieldNotMeasuredDevice = refl

sameDeviceCOPOpen :
  MaxCut.PaymentRow.status MaxCut.sameDeviceCOPRow ≡ MaxCut.openSameObjectAcquisition
sameDeviceCOPOpen = refl

nsNotEmpiricalPayment :
  MaxCut.PaymentRow.status MaxCut.navierStokesRow ≡ MaxCut.structuralPrecedentOnly
nsNotEmpiricalPayment = refl

yangMillsNotEmpiricalPayment :
  MaxCut.PaymentRow.status MaxCut.yangMillsRow ≡ MaxCut.structuralPrecedentOnly
yangMillsNotEmpiricalPayment = refl
