module DASHI.Physics.GR.SchutzholdFrequencyPhaseReadoutExact where

open import DASHI.Core.Prelude

import DASHI.Physics.GR.ControlledEMGravitationalWaveEnergyExchangeExact as Exchange
import DASHI.Physics.GR.SchutzholdEMGWSourceLawExact as Source
import DASHI.Physics.GR.ControlledEMGWReadoutSignPropagationExact as Sign
import DASHI.Physics.GR.ControlledEMGWEnergyFrequencyPhaseCalibrationExact as Calibration

------------------------------------------------------------------------
-- SCHUTZHOLD EQ. (7) / HALF-CYCLE SHIFT -> DELAYED OPTICAL PHASE
--
-- Source content already supplies:
--   Omega^2 = (1-h) Kx^2 + (1+h) Ky^2,
--   Delta Omega = +/- h Omega / 2 for pure x/y propagation,
--   Delta E = +/- h E / 2 per half-cycle,
-- and the equal-length delay-line strategy that accumulates a relative phase
-- from the lasting opposite frequency shifts.
--
-- Hence these symbolic relations are not remaining theory gaps.  What remains
-- is same-object calibration to a concrete laser frequency, delay time and
-- interferometric phase observable.
------------------------------------------------------------------------

data ReadoutSourceLaw : Set where
  sourceDispersionLaw : ReadoutSourceLaw
  pureDirectionFrequencyShiftLaw : ReadoutSourceLaw
  halfCycleEnergyShiftLaw : ReadoutSourceLaw
  delayedRelativePhaseLaw : ReadoutSourceLaw

readoutSourceLawText : ReadoutSourceLaw → String
readoutSourceLawText sourceDispersionLaw =
  Source.sourceEquationText Source.dispersionEquation
readoutSourceLawText pureDirectionFrequencyShiftLaw =
  Source.sourceEquationText Source.pureDirectionFrequencyShiftEquation
readoutSourceLawText halfCycleEnergyShiftLaw =
  Source.sourceEquationText Source.halfCycleEnergyShiftEquation
readoutSourceLawText delayedRelativePhaseLaw =
  Source.sourceEquationText Source.delayedPhaseAccumulationEquation

record SchutzholdFrequencyPhaseReadout
    (interaction : Exchange.EMGWInteractionCarrier) : Set₁ where
  constructor schutzhold-frequency-phase-readout
  field
    calibration : Calibration.EnergyFrequencyPhaseCalibration interaction

    InputOpticalFrequency : Set
    inputOpticalFrequency : InputOpticalFrequency

    GWStrainAmplitude : Set
    gwStrainAmplitude : GWStrainAmplitude

    LastingFrequencyShift : Set
    lastingFrequencyShift : LastingFrequencyShift

    DelayTime : Set
    delayTime : DelayTime

    RelativePhaseShift : Set
    relativePhaseShift : RelativePhaseShift

    Eq7DispersionRealizationReceipt : Set
    eq7DispersionRealizationReceipt : Eq7DispersionRealizationReceipt

    HalfHFrequencyShiftReceipt : Set
    halfHFrequencyShiftReceipt : HalfHFrequencyShiftReceipt

    HalfHEnergyShiftReceipt : Set
    halfHEnergyShiftReceipt : HalfHEnergyShiftReceipt

    EqualPathDelayReceipt : Set
    equalPathDelayReceipt : EqualPathDelayReceipt

    FrequencyToPhaseAccumulationReceipt : Set
    frequencyToPhaseAccumulationReceipt : FrequencyToPhaseAccumulationReceipt

    SameInteractionFrequencyReceipt : Set
    sameInteractionFrequencyReceipt : SameInteractionFrequencyReceipt

    SameInteractionPhaseReceipt : Set
    sameInteractionPhaseReceipt : SameInteractionPhaseReceipt

open SchutzholdFrequencyPhaseReadout public

------------------------------------------------------------------------
-- The finite sign theorem and source direction schedule agree on the intended
-- emission/absorption reversal; numerical magnitudes remain calibration data.
------------------------------------------------------------------------

sourceEmissionHasPositiveWorkReadoutSign :
  Sign.exchangeToWorkSign
    (Source.exchangeSign
      (Source.energyFlow Source.hIncreasing Source.xDirection))
  ≡ Sign.positiveReadout
sourceEmissionHasPositiveWorkReadoutSign = refl

sourceAbsorptionHasNegativeWorkReadoutSign :
  Sign.exchangeToWorkSign
    (Source.exchangeSign
      (Source.energyFlow Source.hIncreasing Source.yDirection))
  ≡ Sign.negativeReadout
sourceAbsorptionHasNegativeWorkReadoutSign = refl

record SchutzholdFrequencyPhaseBoundary : Set where
  constructor schutzhold-frequency-phase-boundary
  field
    sourceDispersionFormulaSpecified : Bool
    sourcePureDirectionFrequencyShiftSpecified : Bool
    sourceHalfCycleEnergyShiftSpecified : Bool
    sourceDelayedPhaseStrategySpecified : Bool
    signPropagationToPhaseAlreadyFormalised : Bool
    newIndependentFrequencyLawNeeded : Bool
    newIndependentPhaseLawNeeded : Bool
    concreteLaserFrequencyCalibrationStillRequired : Bool
    concreteDelayCalibrationStillRequired : Bool
    interferometerNoiseAndSensitivityStillRequired : Bool

canonicalSchutzholdFrequencyPhaseBoundary : SchutzholdFrequencyPhaseBoundary
canonicalSchutzholdFrequencyPhaseBoundary =
  schutzhold-frequency-phase-boundary
    true true true true true false false true true true
