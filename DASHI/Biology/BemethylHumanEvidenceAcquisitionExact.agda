module DASHI.Biology.BemethylHumanEvidenceAcquisitionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

record HumanEvidenceAcquisition : Set where
  field
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
  { heatExertionPMID = "9162292"
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
  ; reading = "Indexed human evidence now pays historical controlled heat/exertion physiology, human excretion, disease-context immune outcomes, and human metabolic-marker observations; it still does not pay a molecular target, modern independent performance replication, or same-object exposure-efficacy closure"
  }

controlledHeatEvidencePaid :
  heatExertionDoubleBlindControlled canonicalHumanEvidenceAcquisition ≡ true
controlledHeatEvidencePaid = refl

humanExposurePaid :
  humanExcretionExposureObserved canonicalHumanEvidenceAcquisition ≡ true
humanExposurePaid = refl

humanTargetStillOpen :
  humanTargetEngagementPaid canonicalHumanEvidenceAcquisition ≡ false
humanTargetStillOpen = refl

modernReplicationStillOpen :
  modernPerformanceReplicationPaid canonicalHumanEvidenceAcquisition ≡ false
modernReplicationStillOpen = refl
