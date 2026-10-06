module DASHI.Physics.ExoticGravity.SchutzholdAntigravityTerminalMaxCutExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Laws.GaugeInteractionLaws as Gauge
import DASHI.Physics.Laws.GravityCosmologyLaws as Gravity
import DASHI.Physics.GR.SchutzholdEMGWSourceLawExact as Source
import DASHI.Physics.GR.ControlledEMGravitationalWaveEnergyExchangeExact as Exchange
import DASHI.Physics.GR.ControlledEMGWExchangeFiniteReversalExact as Reversal
import DASHI.Physics.GR.ControlledEMGWReadoutSignPropagationExact as Readout
import DASHI.Physics.GR.MaxwellMetricHodgeStressEnergyExact as MaxwellStress
import DASHI.Physics.GR.ControlledEMGWEnergyFrequencyPhaseCalibrationExact as Calibration
import DASHI.Physics.ExoticGravity.AntigravityControlledGWExchangeCrossPollinationExact as Anti
import DASHI.Physics.YangMills.R144EMGWControlledExchangeInstantiationExact as R144
import DASHI.Physics.YangMills.MaxwellHodgeR144ControlledExchangeWeldExact as MaxwellR144

------------------------------------------------------------------------
-- TERMINAL MAX-CUT FOR THE SCHUTZHOLD CONTROLLED-EXCHANGE LANE
--
-- Everything already present in-repo is consumed here:
--   Maxwell F and metric-dependent Hodge star
--   weak-field gravitational-wave carrier
--   R144 metric/stress first-variation machinery
--   controlled exchange/reversal algebra
--   SI Planck/frequency authority
--   antigravity ordinary-vs-alternative same-object residual comparator.
--
-- The remaining fields below are deliberately physical same-object/calibration
-- receipts; no second Maxwell, Hodge, GR, SI or antigravity theory is invented.
------------------------------------------------------------------------

record SchutzholdPhysicalRealisation
    (maxwell : Gauge.MaxwellFieldLaw)
    (state : MaxwellStress.MaxwellMetricHodgeState maxwell)
    (stress : MaxwellStress.MaxwellHilbertStressEnergy maxwell state)
    (gravity : Gravity.EinsteinGravityLaw)
    (wave : Gravity.GravitationalWaveLaw gravity) : Set₁ where
  constructor schutzhold-physical-realisation
  field
    maxwellR144 :
      MaxwellR144.MaxwellHodgeR144ExchangeWeld maxwell state stress

    calibration :
      Calibration.EnergyFrequencyPhaseCalibration
        (MaxwellR144.interactionFromMaxwellHodge maxwellR144)

    SourceHamiltonianSameObjectReceipt : Set
    sourceHamiltonianSameObjectReceipt : SourceHamiltonianSameObjectReceipt

    SourceEnergyTransferSameObjectReceipt : Set
    sourceEnergyTransferSameObjectReceipt : SourceEnergyTransferSameObjectReceipt

    SourceDispersionSameObjectReceipt : Set
    sourceDispersionSameObjectReceipt : SourceDispersionSameObjectReceipt

    SourceHalfCycleEnergyShiftSameObjectReceipt : Set
    sourceHalfCycleEnergyShiftSameObjectReceipt :
      SourceHalfCycleEnergyShiftSameObjectReceipt

    DelayedPhaseSameObjectReceipt : Set
    delayedPhaseSameObjectReceipt : DelayedPhaseSameObjectReceipt

    WeakFieldGWIsSameMetricPerturbationReceipt : Set
    weakFieldGWIsSameMetricPerturbationReceipt :
      WeakFieldGWIsSameMetricPerturbationReceipt

open SchutzholdPhysicalRealisation public

record SchutzholdAntigravityComparison
    {maxwell state stress gravity wave}
    (physical :
      SchutzholdPhysicalRealisation maxwell state stress gravity wave) : Set₁ where
  constructor schutzhold-antigravity-comparison
  field
    ordinaryPrediction : Anti.AttributedExchangePrediction
    alternativePrediction : Anti.AttributedExchangePrediction
    observation : Anti.ControlledExchangeObservation

    comparison :
      Anti.SameObjectExchangeComparison
        ordinaryPrediction alternativePrediction observation

    ordinaryIsGR :
      Anti.comparator ordinaryPrediction ≡ Anti.ordinaryGRExchangeComparator

    alternativeIsAlternative :
      Anti.comparator alternativePrediction
      ≡ Anti.alternativeCouplingExchangeComparator

    OrdinaryUsesPhysicalInteractionReceipt : Set
    ordinaryUsesPhysicalInteractionReceipt :
      OrdinaryUsesPhysicalInteractionReceipt

    AlternativeUsesSamePhysicalInteractionReceipt : Set
    alternativeUsesSamePhysicalInteractionReceipt :
      AlternativeUsesSamePhysicalInteractionReceipt

    ObservationUsesSamePhysicalInteractionReceipt : Set
    observationUsesSamePhysicalInteractionReceipt :
      ObservationUsesSamePhysicalInteractionReceipt

open SchutzholdAntigravityComparison public

------------------------------------------------------------------------
-- Source-routing theorems imported/paid directly.
------------------------------------------------------------------------

sourceEmissionFirstHalf :
  Source.exchangeSign (Source.energyFlow Source.hIncreasing Source.xDirection)
  ≡ Exchange.emissionLike
sourceEmissionFirstHalf = Source.sourceHalfCycleScheduleEmission

sourceEmissionSecondHalf :
  Source.exchangeSign (Source.energyFlow Source.hDecreasing Source.yDirection)
  ≡ Exchange.emissionLike
sourceEmissionSecondHalf = Source.sourceHalfCycleScheduleEmissionSecondHalf

sourceAbsorptionFirstHalf :
  Source.exchangeSign (Source.energyFlow Source.hIncreasing Source.yDirection)
  ≡ Exchange.absorptionLike
sourceAbsorptionFirstHalf = Source.sourceOppositeScheduleAbsorption

sourceAbsorptionSecondHalf :
  Source.exchangeSign (Source.energyFlow Source.hDecreasing Source.xDirection)
  ≡ Exchange.absorptionLike
sourceAbsorptionSecondHalf = Source.sourceOppositeScheduleAbsorptionSecondHalf

------------------------------------------------------------------------
-- Terminal frontier: only genuinely physical welding/calibration remains.
------------------------------------------------------------------------

record SchutzholdTerminalFrontier : Set where
  constructor schutzhold-terminal-frontier
  field
    sourceEquationsFormalised : Bool
    directionPhaseReversalFormalised : Bool
    maxwellFieldReused : Bool
    metricDependentHodgeReused : Bool
    r144StressVariationReused : Bool
    weakFieldGWInterfaceReused : Bool
    planckFrequencyAuthorityReused : Bool
    antigravityResidualComparatorReused : Bool

    duplicateMaxwellNeeded : Bool
    duplicateHodgeNeeded : Bool
    duplicateSIConstantsNeeded : Bool
    duplicateAntigravityComparatorNeeded : Bool

    hilbertStressVariationPhysicalWeldOpen : Bool
    gwToR144MetricTangentPhysicalWeldOpen : Bool
    emStressToR144InsertionPhysicalWeldOpen : Bool
    sourceEq5ToInteractionWorkNormalizationOpen : Bool
    sourceEq7ToMeasuredFrequencyCalibrationOpen : Bool
    delayedPathFrequencyToPhaseCalibrationOpen : Bool
    apparatusCalibrationAndNoiseModelOpen : Bool

canonicalSchutzholdTerminalFrontier : SchutzholdTerminalFrontier
canonicalSchutzholdTerminalFrontier =
  schutzhold-terminal-frontier
    true true true true true true true true
    false false false false
    true true true true true true true
