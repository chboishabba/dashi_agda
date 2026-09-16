module DASHI.Environment.BiocontrolCalibratedEcologicalClassificationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Environment.BiocontrolChemistryObservationFibreExact as Chemistry

------------------------------------------------------------------------
-- CALIBRATED CHEMISTRY -> ECOLOGICAL CATEGORY BRIDGE
--
-- A physical/chemical observation does not classify itself.  Classification
-- depends on a declared consumer plus site, season, time window, protocol,
-- uncertainty and validation context.  The repository therefore blocks the
-- shortcut "SI number -> universal hard ecological threshold".
------------------------------------------------------------------------

data EcologicalClass : Set where
  oxygenLow oxygenRecovered : EcologicalClass
  reboundElevated reboundReduced : EcologicalClass
  classificationUnresolved : EcologicalClass

data ThresholdDecision : Set where
  belowDeclaredBand aboveDeclaredBand withinUncertaintyBand : ThresholdDecision

classFromDecision : ThresholdDecision → EcologicalClass
classFromDecision belowDeclaredBand = oxygenLow
classFromDecision aboveDeclaredBand = oxygenRecovered
classFromDecision withinUncertaintyBand = classificationUnresolved

record CalibrationContext : Set where
  constructor calibrationContext
  field
    siteIdentityReference : String
    waterbodyReference : String
    seasonReference : String
    samplingWindowReference : String
    targetConsumerReference : String
    biologicalContextReference : String
    chemistryObservationReference : String
    thresholdRuleReference : String
    uncertaintyRuleReference : String
    measurementProtocolReference : String
    calibrationSourceReference : String
    localValidationReference : String
    localValidationPaid : Bool

open CalibrationContext public

canonicalCalibrationContext : CalibrationContext
canonicalCalibrationContext = calibrationContext
  "site identity required before ecological classification"
  "waterbody/catchment identity required"
  "season/thermal regime required"
  "sampling instant or aggregation window required"
  "consumer must be named: oxygen/decomposition, rebound, restoration, or other"
  "species/community and exposure-history context required where relevant"
  "consume chemistry-indexed observation fibre; do not classify from unit label alone"
  "threshold/band rule must be externally or locally justified"
  "uncertainty and near-threshold handling must be explicit"
  "sensor/assay/sample protocol must be source bound"
  "classification source must be attributed separately from BIPM/SI authority"
  "no Springfield-Lakes local validation receipt has been acquired in this fixture"
  false

record CalibratedClassificationReceipt : Set where
  constructor calibratedClassificationReceipt
  field
    chemistryObservation : Chemistry.ChemistryObservationFibre
    context : CalibrationContext
    decision : ThresholdDecision
    outputClass : EcologicalClass
    decisionMapsToOutput : classFromDecision decision ≡ outputClass
    empiricalObservationPaid : Bool
    thresholdCalibrationPaid : Bool
    uncertaintyHandlingPaid : Bool
    createsInterventionAuthority : Bool

open CalibratedClassificationReceipt public

canonicalUnresolvedClassification : CalibratedClassificationReceipt
canonicalUnresolvedClassification = calibratedClassificationReceipt
  Chemistry.canonicalChemistryObservationFibre
  canonicalCalibrationContext
  withinUncertaintyBand
  classificationUnresolved
  refl
  false
  false
  true
  false

------------------------------------------------------------------------
-- Counterexample-driven local repair of threshold semantics.
------------------------------------------------------------------------

data ThresholdModel : Set where
  universalHardThreshold : ThresholdModel
  contextualThreshold : ThresholdModel

data ThresholdRefines : ThresholdModel → ThresholdModel → Set where
  universalToContextual : ThresholdRefines universalHardThreshold contextualThreshold

ThresholdAdmissible : ThresholdModel → Set
ThresholdAdmissible universalHardThreshold = ⊤
ThresholdAdmissible contextualThreshold = ⊤

ThresholdConsumerAdequate : ThresholdModel → Set
ThresholdConsumerAdequate universalHardThreshold = ⊥
ThresholdConsumerAdequate contextualThreshold = ⊤

thresholdDescriptionLength : ThresholdModel → Nat
thresholdDescriptionLength universalHardThreshold = 1
thresholdDescriptionLength contextualThreshold = 2

thresholdModelReference : ThresholdModel → String
thresholdModelReference universalHardThreshold =
  "context-erased universal ecological threshold"
thresholdModelReference contextualThreshold =
  "site/season/window/protocol/uncertainty/context-indexed classification rule"

thresholdProblem : MDL.ConsumerMDLProblem
thresholdProblem = MDL.consumerMDLProblem
  ThresholdModel
  ThresholdAdmissible
  ThresholdConsumerAdequate
  thresholdDescriptionLength
  ThresholdRefines
  thresholdModelReference
  "finite repository-local threshold-model rank; not field cost or scientific certainty"
  "context-sensitive ecological classification consumer"

universalThresholdCounterexample :
  MDL.ConsumerCounterexample thresholdProblem universalHardThreshold
universalThresholdCounterexample = MDL.consumerCounterexample
  ⊤
  tt
  (λ inadequate → inadequate)
  "universal hard threshold erases site/season/protocol/uncertainty coordinates"
  "same nominal measurement can require different classification handling when context or uncertainty differs"

universalToContextualRepair :
  MDL.LocalRefinementRepair
    thresholdProblem universalHardThreshold contextualThreshold
universalToContextualRepair = MDL.localRefinementRepair
  universalThresholdCounterexample
  universalToContextual
  tt
  tt
  "reopen site, season, sampling window, biological context, protocol, calibration provenance and uncertainty before classification"

contextualRepairProvidesEligibility :
  MDL.Eligible thresholdProblem contextualThreshold
contextualRepairProvidesEligibility =
  MDL.repairProvidesEligibleRefinement universalToContextualRepair

data ThresholdNeighbourhoodAddress : Set where
  ecologicalThresholdFamily : ThresholdNeighbourhoodAddress

thresholdNeighbourhood : MDL.RefinementNeighbourhood thresholdProblem
thresholdNeighbourhood = MDL.refinementNeighbourhood
  ThresholdNeighbourhoodAddress
  (λ model → ecologicalThresholdFamily)
  (λ left right → ⊤)
  (λ coarse fine refinement → tt)
  "ecological classification family: universal hard threshold -> contextual calibrated threshold"

thresholdRepairStaysLocal :
  MDL.sameNeighbourhood thresholdNeighbourhood
    (MDL.address thresholdNeighbourhood universalHardThreshold)
    (MDL.address thresholdNeighbourhood contextualThreshold)
thresholdRepairStaysLocal =
  MDL.repairStaysInDeclaredNeighbourhood
    thresholdNeighbourhood universalToContextualRepair

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record BiocontrolCalibrationBoundary : Set where
  constructor biocontrolCalibrationBoundary
  field
    siNumberDeterminesEcologicalClassWithoutCalibration : Bool
    siNumberDeterminesEcologicalClassWithoutCalibrationIsFalse :
      siNumberDeterminesEcologicalClassWithoutCalibration ≡ false

    oneUniversalThresholdFitsEverySiteSeasonConsumer : Bool
    oneUniversalThresholdFitsEverySiteSeasonConsumerIsFalse :
      oneUniversalThresholdFitsEverySiteSeasonConsumer ≡ false

    uncertaintyBandCanRemainUnresolved : Bool
    uncertaintyBandCanRemainUnresolvedIsTrue :
      uncertaintyBandCanRemainUnresolved ≡ true

    contextualRepairInventsMeasurement : Bool
    contextualRepairInventsMeasurementIsFalse :
      contextualRepairInventsMeasurement ≡ false

    thresholdCitationCreatesDeploymentAuthority : Bool
    thresholdCitationCreatesDeploymentAuthorityIsFalse :
      thresholdCitationCreatesDeploymentAuthority ≡ false

    localValidationStillRequiredForSiteSpecificPromotion : Bool
    localValidationStillRequiredForSiteSpecificPromotionIsTrue :
      localValidationStillRequiredForSiteSpecificPromotion ≡ true

canonicalBiocontrolCalibrationBoundary : BiocontrolCalibrationBoundary
canonicalBiocontrolCalibrationBoundary = biocontrolCalibrationBoundary
  false refl
  false refl
  true refl
  false refl
  false refl
  true refl
