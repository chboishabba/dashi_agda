module DASHI.Physics.Motors.SmithFilsingerMidpointPhaseWorkExact where

-- Finite conditional same-boundary power accounting, + source provenance.
-- User-origin hypothesis: proposed portable common-midpoint / opposed branches;
-- not a completed original netlist, calibrated Earth source, or Maxwell PDE.
-- Reuses existing typed energy, flight, reflection and source owners.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; _+_)
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound
import DASHI.Physics.Motors.SmithFilsingerTimeIndexedTransferExact as Transfer
import DASHI.Physics.Motors.SmithFilsingerReflectedPortBidiExact as Reflect
import DASHI.Physics.Motors.SmithFilsingerSunEarthCoupledSourceExact as Solar

-- Explicit nonnegative incident AND outgoing quantities. Signed natural
-- work is the difference, NOT an unsigned presumed natural input.
record MidpointTwoPortWorkWindow : Set where
  constructor midpointTwoPortWorkWindow
  field
    naturalIncident controllerIncident initialStored : Nat
    naturalOutgoing controllerOutgoing usefulWork internalLoss finalStored : Nat
    completeBoundaryBalance :
      (naturalIncident + controllerIncident) + initialStored
        ≡ usefulWork +
          (internalLoss + (naturalOutgoing + (controllerOutgoing + finalStored)))

availableIncidentAndStorage : MidpointTwoPortWorkWindow → Nat
availableIncidentAndStorage r =
  (MidpointTwoPortWorkWindow.naturalIncident r
   + MidpointTwoPortWorkWindow.controllerIncident r)
   + MidpointTwoPortWorkWindow.initialStored r

usefulNoGreaterThanIncidentAndStorage :
  (r : MidpointTwoPortWorkWindow) →
  Bound._≤_ (MidpointTwoPortWorkWindow.usefulWork r)
             (availableIncidentAndStorage r)
usefulNoGreaterThanIncidentAndStorage r =
  Bound.transportUpper
    (Bound.sym (MidpointTwoPortWorkWindow.completeBoundaryBalance r))
    (Bound.≤-append (MidpointTwoPortWorkWindow.usefulWork r)
      (MidpointTwoPortWorkWindow.internalLoss r +
        (MidpointTwoPortWorkWindow.naturalOutgoing r +
          (MidpointTwoPortWorkWindow.controllerOutgoing r +
            MidpointTwoPortWorkWindow.finalStored r))))

-- Two incident driver quanta -> one useful, one externally radiated.
-- A signal at an Earth-facing port is not automatically Earth-sourced power.
driverOnlyCanRadiateIntoEnvironment : MidpointTwoPortWorkWindow
driverOnlyCanRadiateIntoEnvironment =
  midpointTwoPortWorkWindow 0 2 0 1 0 1 0 0 refl

driverOnlyNaturalIncZero :
  MidpointTwoPortWorkWindow.naturalIncident
    driverOnlyCanRadiateIntoEnvironment ≡ 0
driverOnlyNaturalIncZero = refl

driverOnlyEnvironmentOutPositive :
  MidpointTwoPortWorkWindow.naturalOutgoing
    driverOnlyCanRadiateIntoEnvironment ≡ 1
driverOnlyEnvironmentOutPositive = refl

record NoBoundaryInputCycle : Set where
  constructor noBoundaryInputCycle
  field
    usefulWork otherOutputs : Nat
    noEnergyFromAnywhere : zero ≡ usefulWork + otherOutputs

noBoundaryInputNoUsefulLoad : (r : NoBoundaryInputCycle) →
  NoBoundaryInputCycle.usefulWork r ≡ zero
noBoundaryInputNoUsefulLoad r =
  Solar.sourceFreeLoadZero
    (NoBoundaryInputCycle.usefulWork r)
    (NoBoundaryInputCycle.otherOutputs r)
    (NoBoundaryInputCycle.noEnergyFromAnywhere r)

-- Same phase observation can coexist with different independent sources.
data Contradiction : Set where
data WorkWorld : Set where
  drivenOnly naturallyDriven : WorkWorld
data CoherentBranchPhase : Set where
  steadyDifferential : CoherentBranchPhase

phaseReadout : WorkWorld → CoherentBranchPhase
phaseReadout drivenOnly = steadyDifferential
phaseReadout naturallyDriven = steadyDifferential

data NaturalWorkClass : Set where
  noIndependentNaturalInput independentlyPoweredPort : NaturalWorkClass

naturalWorkClass : WorkWorld → NaturalWorkClass
naturalWorkClass drivenOnly = noIndependentNaturalInput
naturalWorkClass naturallyDriven = independentlyPoweredPort

classesAreDifferent :
  noIndependentNaturalInput ≡ independentlyPoweredPort → Contradiction
classesAreDifferent ()

PhaseReadoutDeterminesNaturalWork : Set
PhaseReadoutDeterminesNaturalWork =
  (a b : WorkWorld) →
    phaseReadout a ≡ phaseReadout b →
      naturalWorkClass a ≡ naturalWorkClass b

phaseReadoutAloneCannotIdentifyNaturalWork :
  PhaseReadoutDeterminesNaturalWork → Contradiction
phaseReadoutAloneCannotIdentifyNaturalWork f =
  classesAreDifferent (f drivenOnly naturallyDriven refl)

-- Source regime and what is actually phase-referenced are separate types.
-- A fixed source with naturally supplied DC bias needs no RF-wave phase lock.
data EnvironmentalSourceRegime : Set where
  independentCoherentWave independentDCBias nonlinearSlowSource :
    EnvironmentalSourceRegime

data PhaseReference : Set where
  controllerBranchToBranch externalSourceToController : PhaseReference

dcBiasIsNotIndependentWave :
  independentDCBias ≡ independentCoherentWave → Contradiction
dcBiasIsNotIndependentWave ()

internalTimingIsNotExternalPhaseReference :
  controllerBranchToBranch ≡ externalSourceToController → Contradiction
internalTimingIsNotExternalPhaseReference ()

-- All physical witnesses remain uninhabited for the same original object.
record SameOriginalMidpointPhaseAndSourceWorkAdmission : Set₁ where
  field
    selectedConfiguration : Reflect.Configuration
    environmentalPortClass : Solar.SourcePort
    environmentalSourceRegime : EnvironmentalSourceRegime
    selectedPhaseReference : PhaseReference
    selectedFlight : Transfer.RetardedFlight
    actualPortReflection : Reflect.MeasuredReciprocalReflection
    ActualPortablePlateOrEarthPins : Set
    ActualBranchAndInteractionRegionPhaseCrossSpectrum : Set
    MeasuredSourceCoherenceAndIndependentReplenishment : Set
    NonlinearHistoryDependentRetardedMaxwellResponse : Set
    MeasuredSignedNaturalDriverModulatorAndLoadWork : Set
    actualPins : ActualPortablePlateOrEarthPins
    phaseResponse : ActualBranchAndInteractionRegionPhaseCrossSpectrum
    naturalSource : MeasuredSourceCoherenceAndIndependentReplenishment
    retardedOperator : NonlinearHistoryDependentRetardedMaxwellResponse
    signedSourceWork : MeasuredSignedNaturalDriverModulatorAndLoadWork
