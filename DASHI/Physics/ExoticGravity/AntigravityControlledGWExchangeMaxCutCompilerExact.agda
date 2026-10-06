module DASHI.Physics.ExoticGravity.AntigravityControlledGWExchangeMaxCutCompilerExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Laws.GravityCosmologyLaws as Laws
import DASHI.Physics.GR.ControlledEMGravitationalWaveEnergyExchangeExact as Exchange
import DASHI.Physics.GR.ControlledEMGWExchangeFiniteReversalExact as Reversal
import DASHI.Physics.GR.MaxwellGWControlledExchangeSameObjectExact as MaxwellGW
import DASHI.Physics.ExoticGravity.AntigravityControlledGWExchangeCrossPollinationExact as Anti
import DASHI.Physics.YangMills.R144EMGWControlledExchangeInstantiationExact as R144GW

------------------------------------------------------------------------
-- END-TO-END MAX-CUT COMPILER
--
-- This is intentionally a compiler of already-explicit receipts.  It does not
-- manufacture the missing physical EM stress tensor or metric-tangent weld.
-- Once those same-object receipts exist, the rest of the route into the
-- antigravity residual comparator is structural.
------------------------------------------------------------------------

record ControlledGWExchangePhysicalInputs
    (law : Laws.EinsteinGravityLaw)
    (wave : Laws.GravitationalWaveLaw law) : Set₁ where
  constructor controlled-gw-exchange-physical-inputs
  field
    maxwellGW : MaxwellGW.MaxwellGWControlledExchangeWeld law wave
    r144GW : R144GW.R144EMGWStressVariationWeld

    SameInteractionAcrossMaxwellAndR144 : Set
    sameInteractionAcrossMaxwellAndR144 : SameInteractionAcrossMaxwellAndR144

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

    ordinaryUsesPhysicalInteraction : Set
    ordinaryUsesPhysicalInteractionReceipt : ordinaryUsesPhysicalInteraction

    alternativeUsesPhysicalInteraction : Set
    alternativeUsesPhysicalInteractionReceipt : alternativeUsesPhysicalInteraction

    observationUsesPhysicalInteraction : Set
    observationUsesPhysicalInteractionReceipt : observationUsesPhysicalInteraction

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

------------------------------------------------------------------------
-- Finite reversal algebra is already paid independently of the physical weld.
------------------------------------------------------------------------

finiteOrthogonalReversalPaid :
  Reversal.reversalActsOnSign
    Exchange.orthogonalPathExchange Exchange.emissionLike
  ≡ Exchange.absorptionLike
finiteOrthogonalReversalPaid = Reversal.orthogonalPathReversesEmission

finiteHalfCycleReversalPaid :
  Reversal.reversalActsOnSign
    Exchange.halfCyclePhaseExchange Exchange.emissionLike
  ≡ Exchange.absorptionLike
finiteHalfCycleReversalPaid = Reversal.halfCycleReversesEmission

finitePolarizationReversalPaid :
  Reversal.reversalActsOnSign
    Exchange.polarizationExchange Exchange.emissionLike
  ≡ Exchange.absorptionLike
finitePolarizationReversalPaid = Reversal.polarizationReversesEmission

finiteDoubleReversalPaid :
  ∀ reversal sign →
  Reversal.reversalActsOnSign reversal
    (Reversal.reversalActsOnSign reversal sign)
  ≡ sign
finiteDoubleReversalPaid = Reversal.doubleReversalRestoresSign

------------------------------------------------------------------------
-- Frontier accounting.
------------------------------------------------------------------------

record ControlledGWExchangeFrontier : Set where
  constructor controlled-gw-exchange-frontier
  field
    finiteReversalAlgebraClosed : Bool
    canonicalMaxwellFieldCarrierConnected : Bool
    weakFieldGWCarrierConnected : Bool
    antigravityResidualCompilerConnected : Bool
    r144AbstractStressVariationConnected : Bool

    physicalEMStressTensorFromMetricHodgeStillOpen : Bool
    physicalGWToR144MetricTangentSameObjectStillOpen : Bool
    physicalEMStressToR144InsertionSameObjectStillOpen : Bool
    workFunctionalNormalizationStillOpen : Bool
    frequencyPhaseCalibrationStillOpen : Bool

canonicalControlledGWExchangeFrontier : ControlledGWExchangeFrontier
canonicalControlledGWExchangeFrontier =
  controlled-gw-exchange-frontier
    true true true true true
    true true true true true
