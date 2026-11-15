module DASHI.Physics.Motors.MadScience369V2CausalFlightBoundExact where

------------------------------------------------------------------------
-- A finite causal support boundary for motor state observations.
-- Reuses the independently sourced Smith/Filsinger RetardedFlight theorem.
-- Interpreting the integer distance/time conversion as a physical c-bound
-- requires source-selected geometry, clocks and front velocity evidence.
-- This is NOT the continuum Maxwell initial-boundary-value theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Motors.SmithFilsingerTimeIndexedTransferExact as Smith
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound

data Empty : Set where

-- In grid units: path length cannot exceed flight time × the specified
-- maximum number of distance quanta allowed per time quantum.  The maximum
-- cannot be larger than the c-converted grid speed for a physical model.
record SpatialLightConeLeg : Set where
  constructor spatialLightConeLeg
  field
    lengthUnits : Nat
    speedUnitsPerTick : Nat
    flightTicks : Nat
    lightCone : Bound._≤_ lengthUnits (flightTicks * speedUnitsPerTick)

-- For the nonzero-separation case, the speed bound is declared relative to
-- the vacuum causal ceiling.  This model does not identify any real medium.
record SeparatedPhysicalLeg : Set where
  constructor separatedPhysicalLeg
  field
    positiveDistanceRest : Nat
    frontSpeedUnitsPerTick : Nat
    vacuumMaxSpeedUnitsPerTick : Nat
    flightDuration : Nat
    mediumNoFasterThanVacuum :
      Bound._≤_ frontSpeedUnitsPerTick vacuumMaxSpeedUnitsPerTick
    causalFrontCone :
      Bound._≤_ (suc positiveDistanceRest)
                  (flightDuration * frontSpeedUnitsPerTick)

scheduledLeg : Nat → SpatialLightConeLeg → Smith.RetardedFlight
scheduledLeg t leg = Smith.scheduled t (SpatialLightConeLeg.flightTicks leg)

arrivalNotBeforeLaunch : (t : Nat) (leg : SpatialLightConeLeg) →
  Bound._≤_ t (Smith.RetardedFlight.arrival (scheduledLeg t leg))
arrivalNotBeforeLaunch t leg = Smith.arrivalNoEarlier (scheduledLeg t leg)

-- This is a non-tautological exclusion: strictly positive separation cannot
-- be traversed in zero time with any finite discrete speed upper bound.
positiveDistanceNoZeroFlight : (distanceRest speed : Nat) →
  Bound._≤_ (suc distanceRest) (zero * speed) → Empty
positiveDistanceNoZeroFlight distanceRest speed ()

noInstantRemoteLeg : (leg : SeparatedPhysicalLeg) →
  SeparatedPhysicalLeg.flightDuration leg ≡ zero → Empty
noInstantRemoteLeg (separatedPhysicalLeg rest velocity ceiling zero speedBound cone) refl =
  positiveDistanceNoZeroFlight rest velocity cone

-- Unlike a zero-delay schematic wire, a two-hop causal route accounts for
-- both propagation intervals and cannot place the endpoint in the past.
twoHopScheduled : Nat → Nat → Nat → Smith.RetardedFlight
twoHopScheduled start first second = Smith.scheduled start (first + second)

twoHopArrivalNotBeforeStart : (start first second : Nat) →
  Bound._≤_ start
    (Smith.RetardedFlight.arrival (twoHopScheduled start first second))
twoHopArrivalNotBeforeStart start first second =
  Smith.arrivalNoEarlier (twoHopScheduled start first second)

record V2SpatialPropagationAdmission : Set₁ where
  field
    SelectedPhysicalCableAndCoilGeometry : Set
    SpecifiedMediumFrontSpeedNoGreaterThanC : Set
    RetardedMaxwellOrTransmissionLineLaw : Set
    ClockSynchronisationAndPathDelay : Set
    QuasistaticApproximationErrorBound : Set
    originalGeometry : SelectedPhysicalCableAndCoilGeometry
    speedEvidence : SpecifiedMediumFrontSpeedNoGreaterThanC
    fieldLaw : RetardedMaxwellOrTransmissionLineLaw
    clockEvidence : ClockSynchronisationAndPathDelay
    errorBound : QuasistaticApproximationErrorBound
