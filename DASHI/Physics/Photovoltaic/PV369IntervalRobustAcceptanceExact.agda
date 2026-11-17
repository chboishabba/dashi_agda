module DASHI.Physics.Photovoltaic.PV369IntervalRobustAcceptanceExact where

-- PV P7: conservative measured-interval acceptance.
-- Solar upper bound and electrical lower bound refer to same aperture,
-- temperature, spectrum, acquisition window and instrument evidence.
-- Strict positivity of a 369 advantage must use the conventional
-- device's UPPER bound, not the conventional point estimate.
--
-- Prior owners reused: inductive Nat <= from Circuit36927RecoveryEnergyBound;
-- PV369NetHalfThresholdExact, PV369MatchedDevicePhysicalAdvantageExact;
-- PV369FourJunctionOpticsToMeasuredIVExact and its source-specific data.
-- All physical interval/measurement witnesses remain UNINHABITED.
-- This is conditional exact arithmetic, not calibration or certification.
-- Agda Golden kernel check OPEN.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound
import DASHI.Physics.Photovoltaic.PV369NetHalfThresholdExact as Net
import DASHI.Physics.Photovoltaic.PV369MatchedDevicePhysicalAdvantageExact as Matched
import DASHI.Physics.Photovoltaic.PV369FourJunctionOpticsToMeasuredIVExact as Optics

-- Import original non-strict witness. A new transitivity proof is reused
-- for 50% and matched-control interval no-go without fake instrument data.
leTrans : {a b c : Nat} -> Bound._≤_ a b ->
  Bound._≤_ b c -> Bound._≤_ a c
leTrans Bound.z≤n _ = Bound.z≤n
leTrans (Bound.s≤s ab) (Bound.s≤s bc) =
  Bound.s≤s (leTrans ab bc)

data False : Set where

-- Both first- and second-device lower+upper values are *MEASURED* bounds
-- on one identical physical power/energy unit, not percentages inferred
-- from assumed sampling distributions or one-sigma errors.
record MeasuredPVPowerInterval : Set where
  field
    solarLower solarUpper : Nat
    netElectricLower netElectricUpper : Nat
    observedSolar observedNetElectric : Nat
    solarLowerSound : Bound._≤_ solarLower observedSolar
    solarUpperSound : Bound._≤_ observedSolar solarUpper
    netLowerSound : Bound._≤_ netElectricLower observedNetElectric
    netUpperSound : Bound._≤_ observedNetElectric netElectricUpper

    sameMeasuredApertureTimeAndSpectrum : String
    calibratedSpectralMismatchSource : String
    irradianceSpatialNonuniformitySource : String
    irradianceTemporalInstabilitySource : String
    calibratedJVCurrentAndVoltageSource : String
    calibratedConverterAndAuxiliaryCostSource : String
    originalRawMeasurementDigestAndSample : String

open MeasuredPVPowerInterval public

record RobustStrictNetHalf : Set where
  field
    measured : MeasuredPVPowerInterval
    strictWorstCaseNetHalf :
      Bound._≤_ (suc (solarUpper measured))
        (netElectricLower measured + netElectricLower measured)

record RobustMatched369Advantage : Set where
  field
    conventional proposed369 : MeasuredPVPowerInterval
    physicallyDistinctMaterialAndOperation : String
    sameSolarReferenceAndSpectralResponse : String
    sameApertureExposureAndTemperature : String
    matchedNo369Source : String
    independentlyVerifiedObservation : String
    strictWorstCaseAdvantage :
      Bound._≤_
        (suc (netElectricUpper conventional))
        (netElectricLower proposed369)

-- A robust half-solar certificate rules out even the WORST case in
-- which observed net has its lower bound and solar has its upper bound.
-- We prove its relevance to the *observed* solar and electric values
-- using only the original Nat constructor and transitivity.
-- Doubling monotonicity requires the existing library's Nat addition
-- compatibility lemma. We deliberately do NOT fake it using refl or
-- direct successor induction; source interval acceptance below keeps
-- its strict premise until a native kernel-confirmed transfer is available.

-- Interval crossing a tied 50% lower bound cannot pass.
strictHalfTieImpossible :
  (solar : Nat) ->
  Bound._≤_ (suc solar) solar -> False
strictHalfTieImpossible zero ()
strictHalfTieImpossible (suc solar) (Bound.s≤s witness) =
  strictHalfTieImpossible solar witness

-- If a candidate's net LOWER <= control's net UPPER, a positive
-- lower-vs-upper advantage is impossible. A strict certificate cannot
-- be created simply by two overlapping intervals.
robustOverlappingCannotProveAdvantage :
  (control candidate : MeasuredPVPowerInterval) ->
  Bound._≤_ (netElectricLower candidate) (netElectricUpper control) ->
  Bound._≤_ (suc (netElectricUpper control))
    (netElectricLower candidate) -> False
robustOverlappingCannotProveAdvantage control candidate lowToHigh highToLow =
  strictHalfTieImpossible
    (netElectricUpper control)
    (leTrans highToLow lowToHigh)

-- No evidence is manufactured for either robustness record. In
-- particular, Strings and sample hashes alone are not metrological
-- interval proofs. Physically correct +/- uncertainties must be supplied.
