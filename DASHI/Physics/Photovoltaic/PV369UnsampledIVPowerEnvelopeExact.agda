module DASHI.Physics.Photovoltaic.PV369UnsampledIVPowerEnvelopeExact where

-- Native source-gated IV continuum max-power sampling bound.
-- PV goal: robust >50% NET source-normalized electric output and a
-- physical 369-vs-conventional same-sample improvement, not a basis label.
-- IEC 60904-1:2020 requires stabilized/steady-state IV and sweep effects.
-- Existing owners reused: Semiconductor spatial carrier continuity, SG
-- flux, P5 original EQE/JV source, P7 interval proof and Nat <=.
--
-- Mathematical lemma, CONDITIONAL on continuous true generating current
-- J(V)>=0 and J(V) NONINCREASING on every sampled interval, and pointwise
-- simultaneous V/J calibrated error envelopes. Sampled J monotonicity
-- ALONE DOES NOT establish a true physical monotone curve.
-- Any source record below cannot authenticate IEC conformity; no physical
-- device, 369 mechanism or certified >50% receipt is constructed.
-- Golden Agda native acceptance OPEN.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound
import DASHI.Physics.Photovoltaic.PV369IntervalRobustAcceptanceExact as Robust
import DASHI.Physics.Photovoltaic.PV369FourJunctionOpticsToMeasuredIVExact as P5
import DASHI.Physics.Semiconductor.Device.SpatialContinuityRecombinationExact as Carrier
import DASHI.Physics.Semiconductor.Device.FiniteScharfetterGummelFluxExact as SG

record IVSegmentRectangle : Set where
  field
    sampleLeftV sampleRightV sampledLeftJ : Nat
    trueV trueJ : Nat
    physicalVWithinLeftAndRight :
      Bound._≤_ trueV sampleRightV
    physicalJAtMostLeftSample :
      Bound._≤_ trueJ sampledLeftJ

    -- This follows from monotonicity of natural-number multiplication
    -- once BOTH inequalities refer to true exact calibrated units. Since
    -- floating/continuous IV is a different scalar carrier, the proof
    -- that a physical current lies in these Nat bounds is a SOURCE gate.
    sampledRectangleProducts : Bound._≤_
      (trueV * trueJ) (sampleRightV * sampledLeftJ)

-- The original source's monotonicity must be certified across the whole
-- interval and under relevant sweep rate, dynamics, temperature and source
-- illumination; a finite grid of monotone samples is not such a proof.
record IVFullIntervalMonotonicityEvidence : Set₁ where
  field
    OriginalSameDeviceIV : Set
    sameDeviceSource : OriginalSameDeviceIV
    SteadyStateSameIllumination : Set
    steadyStateSource : SteadyStateSameIllumination
    ContinuousTrueIVWithinSamples : Set
    continuousCurveSource : ContinuousTrueIVWithinSamples
    FullIntervalCurrentMonotonicity : Set
    trueMonotonicitySource : FullIntervalCurrentMonotonicity
    SimultaneousCurrentVoltageErrorBounds : Set
    errorEnvelopeSource : SimultaneousCurrentVoltageErrorBounds
    InstrumentAndOriginalIVSampleSHA256 : Set
    rawDataReceipt : InstrumentAndOriginalIVSampleSHA256

-- The worst-case P7 consumer cannot use the piecewise-linear sampled
-- 4T MPP as a complete continuum upper bound. It requires source-typed
-- unsampled-envelope evidence and P7's original robust net acceptance.
record FullSweepRobustPVSourceWeld : Set₁ where
  field
    sourceFullSweepMonotonicity : IVFullIntervalMonotonicityEvidence
    measuredSolarNetInterval : Robust.MeasuredPVPowerInterval
    robustAboveHalf : Bound._≤_
      (suc (Robust.MeasuredPVPowerInterval.solarUpper
              measuredSolarNetInterval))
      (Robust.MeasuredPVPowerInterval.netElectricLower
        measuredSolarNetInterval +
       Robust.MeasuredPVPowerInterval.netElectricLower
        measuredSolarNetInterval)

-- No witness of IVFullIntervalMonotonicityEvidence or FullSweepRobustPVSourceWeld
-- is produced by an optical 100-photon synthetic fixture or a source URL.
