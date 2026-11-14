module DASHI.Biology.BemethylHumanEvidenceAcquisitionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

record HumanEvidenceAcquisition : Set where
  field
    operatorPerformancePMID : String
    operatorPerformanceSetting : String
    operatorPerformancePlaceboControlled : Bool
    operatorCompensatoryTrackingReportedImprovement : String
    operatorPursuitTrackingErrorReportedRatio : String
    operatorVisualSignalDetectionReportedRatio : String
    operatorAbstractGivesSampleSize : Bool

    heatExertionPMID : String
    heatExertionDose : String
    heatExertionDoubleBlindControlled : Bool
    heatExertionMeasuresGasEnergyExchange : Bool
    heatExertionMeasuresBloodOxygenation : Bool
    heatExertionMeasuresWorkCapacity : Bool
    heatExertionAbstractGivesSampleSize : Bool

    carbonMonoxideHeatPMID : String
    carbonMonoxideHeatHumanVolunteerEvidence : Bool
    carbonMonoxideHeatIncludesPlacebo : Bool
    carbonMonoxideHeatExactAllocationRecovered : Bool

    healthyVolunteerPKPMID : String
    healthyVolunteerPKSingleOralDoseMg : String
    healthyVolunteerPKCmax : String
    healthyVolunteerPKTmax : String
    healthyVolunteerPKObserved : Bool
    healthyVolunteerPKAbstractGivesSampleSize : Bool

    humanExcretionPMID : String
    humanExcretionVolunteerCount : String
    humanExcretionExposureObserved : Bool
    humanExcretionParentDetected : Bool
    humanExcretionGlucuronideDetected : Bool
    humanExcretionIsEfficacyTrial : Bool

    recurrentErysipelasPMID : String
    recurrentErysipelasParticipantCount : String
    recurrentErysipelasPlaceboControlled : Bool
    recurrentErysipelasImmuneOutcomeReported : Bool
    recurrentErysipelasProvesGeneralImmunostimulation : Bool

    neuromuscularPMID : String
    neuromuscularParticipantCount : String
    neuromuscularHumanMetabolicMarkersObserved : Bool
    neuromuscularIdentifiesMolecularTarget : Bool

    humanTargetEngagementPaid : Bool
    modernPerformanceReplicationPaid : Bool
    modernHeatOxygenReplicationPaid : Bool
    exposureEfficacySameObjectPaid : Bool

    reading : String

open HumanEvidenceAcquisition public

canonicalHumanEvidenceAcquisition : HumanEvidenceAcquisition
canonicalHumanEvidenceAcquisition = record
  { operatorPerformancePMID = "3066983"
  ; operatorPerformanceSetting = "simulated space flight and 56-hour continuous work"
  ; operatorPerformancePlaceboControlled = true
  ; operatorCompensatoryTrackingReportedImprovement = "about 10 percent higher"
  ; operatorPursuitTrackingErrorReportedRatio = "1.8 times lower"
  ; operatorVisualSignalDetectionReportedRatio = "2.4 times shorter"
  ; operatorAbstractGivesSampleSize = false
  ; heatExertionPMID = "9162292"
  ; heatExertionDose = "0.5 g single dose"
  ; heatExertionDoubleBlindControlled = true
  ; heatExertionMeasuresGasEnergyExchange = true
  ; heatExertionMeasuresBloodOxygenation = true
  ; heatExertionMeasuresWorkCapacity = true
  ; heatExertionAbstractGivesSampleSize = false
  ; carbonMonoxideHeatPMID = "8087458"
  ; carbonMonoxideHeatHumanVolunteerEvidence = true
  ; carbonMonoxideHeatIncludesPlacebo = true
  ; carbonMonoxideHeatExactAllocationRecovered = false
  ; healthyVolunteerPKPMID = "21870773"
  ; healthyVolunteerPKSingleOralDoseMg = "250"
  ; healthyVolunteerPKCmax = "0.91 +/- 1.05 microgram/ml"
  ; healthyVolunteerPKTmax = "1.06 +/- 0.16 h"
  ; healthyVolunteerPKObserved = true
  ; healthyVolunteerPKAbstractGivesSampleSize = false
  ; humanExcretionPMID = "30346653"
  ; humanExcretionVolunteerCount = "6 healthy volunteers"
  ; humanExcretionExposureObserved = true
  ; humanExcretionParentDetected = true
  ; humanExcretionGlucuronideDetected = true
  ; humanExcretionIsEfficacyTrial = false
  ; recurrentErysipelasPMID = "1942990"
  ; recurrentErysipelasParticipantCount = "66 patients"
  ; recurrentErysipelasPlaceboControlled = true
  ; recurrentErysipelasImmuneOutcomeReported = true
  ; recurrentErysipelasProvesGeneralImmunostimulation = false
  ; neuromuscularPMID = "1664607"
  ; neuromuscularParticipantCount = "21 patients"
  ; neuromuscularHumanMetabolicMarkersObserved = true
  ; neuromuscularIdentifiesMolecularTarget = false
  ; humanTargetEngagementPaid = false
  ; modernPerformanceReplicationPaid = false
  ; modernHeatOxygenReplicationPaid = false
  ; exposureEfficacySameObjectPaid = false
  ; reading = "Indexed human evidence now pays a historical placebo-controlled operator-performance experiment, controlled heat/exertion physiology, healthy-volunteer pharmacokinetic and excretion observations, disease-context immune outcomes, and human metabolic-marker observations; it still does not pay a molecular target, modern independent performance replication, or same-object exposure-efficacy closure"
  }

historicalOperatorPerformancePaid :
  operatorPerformancePlaceboControlled canonicalHumanEvidenceAcquisition ≡ true
historicalOperatorPerformancePaid = refl

controlledHeatEvidencePaid :
  heatExertionDoubleBlindControlled canonicalHumanEvidenceAcquisition ≡ true
controlledHeatEvidencePaid = refl

humanPKPaid : healthyVolunteerPKObserved canonicalHumanEvidenceAcquisition ≡ true
humanPKPaid = refl

humanExposurePaid :
  humanExcretionExposureObserved canonicalHumanEvidenceAcquisition ≡ true
humanExposurePaid = refl

humanTargetStillOpen :
  humanTargetEngagementPaid canonicalHumanEvidenceAcquisition ≡ false
humanTargetStillOpen = refl

modernReplicationStillOpen :
  modernPerformanceReplicationPaid canonicalHumanEvidenceAcquisition ≡ false
modernReplicationStillOpen = refl
