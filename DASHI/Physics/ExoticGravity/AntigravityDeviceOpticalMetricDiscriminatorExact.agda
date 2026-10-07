module DASHI.Physics.ExoticGravity.AntigravityDeviceOpticalMetricDiscriminatorExact where

open import DASHI.Core.Prelude

import DASHI.Physics.ExoticGravity.EngineeredInertialGravitationalHyperfabricExact as Hyper
import DASHI.Physics.ExoticGravity.EngineeredInertialGravitationalBidiExact as Bidi
import DASHI.Physics.ExoticGravity.AntigravitySearchNonGeometricOppositeExact as Search
import DASHI.Physics.ExoticGravity.WeightMetricApparentMassExact as Weight
import DASHI.Physics.ExoticGravity.SchutzholdAntigravityTerminalMaxCutExact as Schutzhold
import DASHI.Physics.Foundations.GRQFTLocalizedAnisotropicRepulsiveShellExact as PositiveG

------------------------------------------------------------------------
-- DEVICE -> SOURCE -> METRIC -> MULTI-CHANNEL OBSERVABLE COMPILER
--
-- The device claim is not represented by one scalar called "antigravity".
-- One controlled device state is projected through ordinary and candidate
-- source/geometry models into weight, free-fall, clock and optical-metric
-- channels.  The optical lane is the Schuetzhold/R144 metric transducer; the
-- weight lane remains a support-force/apparent-mass observable.
------------------------------------------------------------------------

data DeviceObservationChannel : Set where
  weightChannel : DeviceObservationChannel
  freeFallChannel : DeviceObservationChannel
  clockChannel : DeviceObservationChannel
  opticalPhaseChannel : DeviceObservationChannel
  momentumChannel : DeviceObservationChannel
  inertialResponseChannel : DeviceObservationChannel

data DeviceControlReversal : Set where
  transversePathSwap : DeviceControlReversal
  drivePhasePiShift : DeviceControlReversal
  currentDirectionFlip : DeviceControlReversal
  angularMomentumFlip : DeviceControlReversal
  deviceOnOffSwap : DeviceControlReversal

data ReversalParity : Set where
  reversalEven : ReversalParity
  reversalOdd : ReversalParity
  reversalModelSpecific : ReversalParity

data GravitySourceRoute : Set where
  ordinaryGRRoute : GravitySourceRoute
  positiveGActiveStressRouteTag : GravitySourceRoute
  universalNegativeGRoute : GravitySourceRoute
  materialEffectiveNegativeGRoute : GravitySourceRoute
  sourceSpecificEffectiveCouplingRoute : GravitySourceRoute

record DeviceStateModel : Set₁ where
  constructor device-state-model
  field
    DeviceState : Set
    StressEnergy : Set
    Metric : Set
    WeightObservable : Set
    FreeFallObservable : Set
    ClockObservable : Set
    OpticalPhaseObservable : Set
    MomentumObservable : Set
    InertialObservable : Set

    deviceStateToStressEnergy : DeviceState → StressEnergy

    ordinaryMetricPrediction :
      DeviceState → StressEnergy → Metric

    candidateMetricPrediction :
      DeviceState → StressEnergy → Metric

    weightReadout : DeviceState → Metric → WeightObservable
    freeFallReadout : DeviceState → Metric → FreeFallObservable
    clockReadout : DeviceState → Metric → ClockObservable
    opticalMetricReadout : DeviceState → Metric → OpticalPhaseObservable
    momentumReadout : DeviceState → MomentumObservable
    inertialReadout : DeviceState → InertialObservable

open DeviceStateModel public

record DevicePredictions
    (model : DeviceStateModel)
    (state : DeviceState model) : Set₁ where
  constructor device-predictions
  field
    stressEnergy : StressEnergy model
    stressEnergyIsSameDeviceState :
      stressEnergy ≡ deviceStateToStressEnergy model state

    ordinaryMetric : Metric model
    ordinaryMetricIsPrediction :
      ordinaryMetric ≡ ordinaryMetricPrediction model state stressEnergy

    candidateMetric : Metric model
    candidateMetricIsPrediction :
      candidateMetric ≡ candidateMetricPrediction model state stressEnergy

    ordinaryWeight : WeightObservable model
    ordinaryWeightIsPrediction :
      ordinaryWeight ≡ weightReadout model state ordinaryMetric

    candidateWeight : WeightObservable model
    candidateWeightIsPrediction :
      candidateWeight ≡ weightReadout model state candidateMetric

    ordinaryFreeFall : FreeFallObservable model
    ordinaryFreeFallIsPrediction :
      ordinaryFreeFall ≡ freeFallReadout model state ordinaryMetric

    candidateFreeFall : FreeFallObservable model
    candidateFreeFallIsPrediction :
      candidateFreeFall ≡ freeFallReadout model state candidateMetric

    ordinaryClock : ClockObservable model
    ordinaryClockIsPrediction :
      ordinaryClock ≡ clockReadout model state ordinaryMetric

    candidateClock : ClockObservable model
    candidateClockIsPrediction :
      candidateClock ≡ clockReadout model state candidateMetric

    ordinaryOpticalPhase : OpticalPhaseObservable model
    ordinaryOpticalPhaseIsPrediction :
      ordinaryOpticalPhase ≡ opticalMetricReadout model state ordinaryMetric

    candidateOpticalPhase : OpticalPhaseObservable model
    candidateOpticalPhaseIsPrediction :
      candidateOpticalPhase ≡ opticalMetricReadout model state candidateMetric

open DevicePredictions public

------------------------------------------------------------------------
-- MODULATED / LOCK-IN EXPERIMENT
--
-- The controlled device state should be deliberately modulated so any metric
-- response carries the imposed drive frequency/phase.  This turns the metric
-- lane into a synchronous discriminator instead of a DC drift measurement.
------------------------------------------------------------------------

record DeviceModulationExperiment
    (model : DeviceStateModel) : Set₁ where
  constructor device-modulation-experiment
  field
    baselineState : DeviceState model
    drivenState : DeviceState model

    ModulationPhase : Set
    ModulationFrequency : Set
    LockInObservable : Set

    drivePhase : ModulationPhase
    modulationFrequency : ModulationFrequency
    lockInObservable : LockInObservable

    sameApparatusAcrossModulation : Set
    sameApparatusAcrossModulationReceipt : sameApparatusAcrossModulation

    modulationLockInReceipt : Set
    modulationLockInReceiptValue : modulationLockInReceipt

    expectedReversalParity :
      DeviceControlReversal → DeviceObservationChannel → ReversalParity

open DeviceModulationExperiment public

------------------------------------------------------------------------
-- Same-object calibrated comparison.
------------------------------------------------------------------------

record SameObjectDeviceComparison
    (model : DeviceStateModel)
    (state : DeviceState model)
    (predictions : DevicePredictions model state) : Set₁ where
  constructor same-object-device-comparison
  field
    samePhysicalDeviceState : Set
    samePhysicalDeviceStateReceipt : samePhysicalDeviceState

    sameOpticalProbe : Set
    sameOpticalProbeReceipt : sameOpticalProbe

    sameCalibration : Set
    sameCalibrationReceipt : sameCalibration

    ordinaryConfoundersClosed : Set
    ordinaryConfoundersClosedReceipt : ordinaryConfoundersClosed

    CrossChannelConsistency : Set
    crossChannelConsistency : CrossChannelConsistency

    reversalRepresentation :
      DeviceControlReversal → DeviceObservationChannel → ReversalParity → Set

    Residual : Set
    ordinaryResidual : Residual
    candidateResidual : Residual

    ResidualBetter : Residual → Residual → Set
    candidateResidualBetterThanOrdinaryResidual :
      ResidualBetter candidateResidual ordinaryResidual

open SameObjectDeviceComparison public

------------------------------------------------------------------------
-- Cross-channel theorem target.
--
-- A metric-producing candidate should predict one mutually compatible metric
-- object whose projections agree with independent probes.  A weight-only
-- residual does not satisfy this target by itself.
------------------------------------------------------------------------

record MetricCrossChannelWeld
    (model : DeviceStateModel)
    (state : DeviceState model) : Set₁ where
  constructor metric-cross-channel-weld
  field
    inferredMetric : Metric model

    WeightMetricCompatibility : Set
    weightMetricCompatibility : WeightMetricCompatibility

    FreeFallMetricCompatibility : Set
    freeFallMetricCompatibility : FreeFallMetricCompatibility

    ClockMetricCompatibility : Set
    clockMetricCompatibility : ClockMetricCompatibility

    OpticalMetricCompatibility : Set
    opticalMetricCompatibility : OpticalMetricCompatibility

    allChannelsUseSameMetric : Set
    allChannelsUseSameMetricReceipt : allChannelsUseSameMetric

open MetricCrossChannelWeld public

------------------------------------------------------------------------
-- POSITIVE-G / NEGATIVE-ACTIVE-STRESS ROUTE
--
-- The repo already contains an exact finite witness with positive density,
-- anisotropic tension, negative integrated active source and outward exterior
-- response under positive G.  Therefore the device search must compare this
-- route against signed-G alternatives rather than assuming negative G is the
-- only route to a repulsive gravitational response.
------------------------------------------------------------------------

positiveGActiveStressRoute :
  PositiveG.LocalizedAnisotropicRepulsiveShellWitness
positiveGActiveStressRoute =
  PositiveG.canonicalLocalizedAnisotropicRepulsiveShellWitness

existingLocalizedPositiveGRepulsiveShell :
  PositiveG.LocalizedAnisotropicRepulsiveShellWitness
existingLocalizedPositiveGRepulsiveShell = positiveGActiveStressRoute

existingLiTorrKernel : Bidi.CommonMechanismKernel
existingLiTorrKernel = Bidi.liTorrKernel

record PositiveGActiveStressDeviceBoundary : Set where
  constructor positive-g-active-stress-device-boundary
  field
    positiveGActiveStressRouteAlreadyConstructed : Bool
    negativeGRequiredForOutwardExteriorResponse : Bool
    negativeInertialMassRequiredForOutwardExteriorResponse : Bool
    deviceStressTensorStillRequiresPhysicalRealisation : Bool
    exactStaticDeviceMetricStillRequiresSolution : Bool

canonicalPositiveGActiveStressDeviceBoundary :
  PositiveGActiveStressDeviceBoundary
canonicalPositiveGActiveStressDeviceBoundary =
  positive-g-active-stress-device-boundary
    true false false true true

------------------------------------------------------------------------
-- Existing architectural donors remain authoritative.
------------------------------------------------------------------------

existingHyperfabricBoundary : Hyper.ObservableProjectionBoundary
existingHyperfabricBoundary = Hyper.canonicalObservableProjectionBoundary

existingBidiCutset : Bidi.GravityMechanismBidiCutset
existingBidiCutset = Bidi.canonicalGravityMechanismBidiCutset

existingNonGeometricOppositeBoundary :
  Search.AntigravityNonGeometricOppositeBoundary
existingNonGeometricOppositeBoundary =
  Search.canonicalAntigravityNonGeometricOppositeBoundary

existingWeightMetricBoundary : Weight.WeightMetricBoundary
existingWeightMetricBoundary = Weight.canonicalWeightMetricBoundary

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record AntigravityDeviceDiscriminatorBoundary : Set where
  constructor antigravity-device-discriminator-boundary
  field
    weightResidualAloneProvesMetricEngineering : Bool
    opticalPhaseResidualAloneProvesAntigravity : Bool
    crossChannelConsistencyRequiredForMetricClaim : Bool
    reversalRepresentationRequiredForMechanismClaim : Bool
    sameObjectOrdinaryCandidateComparisonRequired : Bool
    couplingSignLabelAloneSuppliesOppositeMetric : Bool
    sourceMustBeResolvedBeforeMetricComparison : Bool
    ordinaryMomentumAndEMChannelsMustClose : Bool
    modulationLockInPreferredToUnmodulatedDCClaim : Bool
    positiveGActiveStressMustRemainLiveSearchRoute : Bool

canonicalAntigravityDeviceDiscriminatorBoundary :
  AntigravityDeviceDiscriminatorBoundary
canonicalAntigravityDeviceDiscriminatorBoundary =
  antigravity-device-discriminator-boundary
    false false true true true false true true true true
