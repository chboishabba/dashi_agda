module DASHI.Physics.ExoticGravity.AntigravityControlledGWExchangeMaxCutCompilerExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Laws.GravityCosmologyLaws as Laws
import DASHI.Physics.GR.ControlledEMGravitationalWaveEnergyExchangeExact as Exchange
import DASHI.Physics.GR.ControlledEMGWExchangeFiniteReversalExact as Reversal
import DASHI.Physics.GR.MaxwellGWControlledExchangeSameObjectExact as MaxwellGW
import DASHI.Physics.GR.MaxwellMetricHodgeStressEnergyExact as MaxwellStress
import DASHI.Physics.GR.ControlledEMGWEnergyFrequencyPhaseCalibrationExact as Calibration
import DASHI.Physics.GR.SchutzholdInteractionWorkNormalizationExact as Work
import DASHI.Physics.GR.SchutzholdFrequencyPhaseReadoutExact as FrequencyPhase
import DASHI.Physics.ExoticGravity.AntigravityControlledGWExchangeCrossPollinationExact as Anti
import DASHI.Physics.YangMills.R144EMGWControlledExchangeInstantiationExact as R144GW

record ControlledGWExchangePhysicalInputs
    (law : Laws.EinsteinGravityLaw)
    (wave : Laws.GravitationalWaveLaw law) : Set₁ where
  constructor controlled-gw-exchange-physical-inputs
  field
    maxwellGW : MaxwellGW.MaxwellGWControlledExchangeWeld law wave
    r144GW : R144GW.R144EMGWStressVariationWeld

    maxwellAndR144InteractionsEqual :
      MaxwellGW.MaxwellGWControlledExchangeWeld.interaction maxwellGW
      ≡ R144GW.R144EMGWStressVariationWeld.interaction r144GW

    PhysicalReversalRealizationReceipt : Set
    physicalReversalRealizationReceipt : PhysicalReversalRealizationReceipt

open ControlledGWExchangePhysicalInputs public

record ControlledGWExchangePredictionInputs
    {law : Laws.EinsteinGravityLaw}
    {wave : Laws.GravitationalWaveLaw law}
    (physical : ControlledGWExchangePhysicalInputs law wave) : Set₁ where
  constructor controlled-gw-exchange-prediction-inputs
  field
    observed : Anti.ControlledExchangeObservation
    ordinary : Anti.AttributedExchangePrediction
    alternative : Anti.AttributedExchangePrediction

    ordinaryUsesPhysicalInteraction :
      Anti.AttributedExchangePrediction.interaction ordinary
      ≡ MaxwellGW.MaxwellGWControlledExchangeWeld.interaction
          (ControlledGWExchangePhysicalInputs.maxwellGW physical)

    alternativeUsesPhysicalInteraction :
      Anti.AttributedExchangePrediction.interaction alternative
      ≡ MaxwellGW.MaxwellGWControlledExchangeWeld.interaction
          (ControlledGWExchangePhysicalInputs.maxwellGW physical)

    observationUsesPhysicalInteraction :
      Anti.ControlledExchangeObservation.interaction observed
      ≡ MaxwellGW.MaxwellGWControlledExchangeWeld.interaction
          (ControlledGWExchangePhysicalInputs.maxwellGW physical)

open ControlledGWExchangePredictionInputs public

record ControlledGWExchangeResidualClosure
    {law : Laws.EinsteinGravityLaw}
    {wave : Laws.GravitationalWaveLaw law}
    (physical : ControlledGWExchangePhysicalInputs law wave)
    (predictions : ControlledGWExchangePredictionInputs physical) : Set₁ where
  constructor controlled-gw-exchange-residual-closure
  field
    comparison :
      Anti.SameObjectExchangeComparison
        (ControlledGWExchangePredictionInputs.ordinary predictions)
        (ControlledGWExchangePredictionInputs.alternative predictions)
        (ControlledGWExchangePredictionInputs.observed predictions)

    ordinaryComparatorCorrect :
      Anti.comparator (ControlledGWExchangePredictionInputs.ordinary predictions)
        ≡ Anti.ordinaryGRExchangeComparator

    alternativeComparatorCorrect :
      Anti.comparator (ControlledGWExchangePredictionInputs.alternative predictions)
        ≡ Anti.alternativeCouplingExchangeComparator

open ControlledGWExchangeResidualClosure public

finiteOrthogonalReversalPaid :
  Reversal.reversalActsOnSign Exchange.orthogonalPathExchange Exchange.emissionLike
  ≡ Exchange.absorptionLike
finiteOrthogonalReversalPaid = Reversal.orthogonalPathReversesEmission

finiteHalfCycleReversalPaid :
  Reversal.reversalActsOnSign Exchange.halfCyclePhaseExchange Exchange.emissionLike
  ≡ Exchange.absorptionLike
finiteHalfCycleReversalPaid = Reversal.halfCycleReversesEmission

finitePolarizationReversalPaid :
  Reversal.reversalActsOnSign Exchange.polarizationExchange Exchange.emissionLike
  ≡ Exchange.absorptionLike
finitePolarizationReversalPaid = Reversal.polarizationReversesEmission

finiteDoubleReversalPaid :
  ∀ reversal sign →
  Reversal.reversalActsOnSign reversal
    (Reversal.reversalActsOnSign reversal sign) ≡ sign
finiteDoubleReversalPaid = Reversal.doubleReversalRestoresSign

existingMaxwellMetricHodgeBoundary : MaxwellStress.MaxwellMetricHodgeStressBoundary
existingMaxwellMetricHodgeBoundary = MaxwellStress.canonicalMaxwellMetricHodgeStressBoundary

existingEnergyFrequencyBoundary : Calibration.EnergyFrequencyPhaseBoundary
existingEnergyFrequencyBoundary = Calibration.canonicalEnergyFrequencyPhaseBoundary

existingWorkLawBoundary : Work.SchutzholdWorkNormalizationBoundary
existingWorkLawBoundary = Work.canonicalSchutzholdWorkNormalizationBoundary

existingFrequencyPhaseLawBoundary : FrequencyPhase.SchutzholdFrequencyPhaseBoundary
existingFrequencyPhaseLawBoundary = FrequencyPhase.canonicalSchutzholdFrequencyPhaseBoundary

record ControlledGWExchangeFrontier : Set where
  constructor controlled-gw-exchange-frontier
  field
    finiteReversalAlgebraClosed : Bool
    canonicalMaxwellFieldCarrierConnected : Bool
    existingMetricDependentHodgeConnected : Bool
    weakFieldGWCarrierConnected : Bool
    antigravityResidualCompilerConnected : Bool
    r144AbstractStressVariationConnected : Bool
    exactSIPlanckFrequencyAuthorityConnected : Bool
    sourceWorkLawConnected : Bool
    sourceFrequencyPhaseLawConnected : Bool
    literalInteractionCarrierEqualitiesEnforced : Bool

    newIndependentMaxwellTheoryStillNeeded : Bool
    newIndependentHodgeTheoryStillNeeded : Bool
    newIndependentConstantsTableStillNeeded : Bool
    newIndependentWorkLawStillNeeded : Bool
    newIndependentFrequencyPhaseLawStillNeeded : Bool

    hilbertEMStressMetricVariationSameObjectStillOpen : Bool
    physicalGWToR144MetricTangentSameObjectStillOpen : Bool
    physicalEMStressToR144InsertionSameObjectStillOpen : Bool
    renormalizedExpectationAndIntegralNumericsStillOpen : Bool
    experimentSpecificLaserDelayNoiseCalibrationStillOpen : Bool

canonicalControlledGWExchangeFrontier : ControlledGWExchangeFrontier
canonicalControlledGWExchangeFrontier =
  controlled-gw-exchange-frontier
    true true true true true true true true true true
    false false false false false
    true true true true true
