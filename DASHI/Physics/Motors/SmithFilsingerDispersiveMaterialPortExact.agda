module DASHI.Physics.Motors.SmithFilsingerDispersiveMaterialPortExact where

-- Finite conditional source/port ledger. Not real-device Maxwell proof.
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound

-- Positive and recovered material-parameter work are distinct ports.
record MemoryMaterialPortLedger : Set where
  constructor memoryMaterialPortLedger
  field
    environmentStoredInitially environmentRecharged : Nat
    driverWork materialModulatorInput localInitiallyStored : Nat
    usefulWork resistiveAndRelaxationLoss feedLoss : Nat
    materialModulatorRecovery environmentStoredFinally localFinallyStored : Nat
    fullBalance :
      (((environmentStoredInitially + environmentRecharged)
        + driverWork) + (materialModulatorInput + localInitiallyStored))
      ≡ usefulWork + ((resistiveAndRelaxationLoss + feedLoss)
        + (materialModulatorRecovery
          + (environmentStoredFinally + localFinallyStored)))

initialPlusAllInputs : MemoryMaterialPortLedger → Nat
initialPlusAllInputs r =
   (((MemoryMaterialPortLedger.environmentStoredInitially r
      + MemoryMaterialPortLedger.environmentRecharged r)
      + MemoryMaterialPortLedger.driverWork r)
      + (MemoryMaterialPortLedger.materialModulatorInput r
        + MemoryMaterialPortLedger.localInitiallyStored r))

loadCannotExceedAllBoundaryInputs : (r : MemoryMaterialPortLedger) →
  Bound._≤_ (MemoryMaterialPortLedger.usefulWork r) (initialPlusAllInputs r)
loadCannotExceedAllBoundaryInputs r =
  Bound.transportUpper
    (Bound.sym (MemoryMaterialPortLedger.fullBalance r))
    (Bound.≤-append (MemoryMaterialPortLedger.usefulWork r)
      ((MemoryMaterialPortLedger.resistiveAndRelaxationLoss r
        + MemoryMaterialPortLedger.feedLoss r)
       + (MemoryMaterialPortLedger.materialModulatorRecovery r
        + (MemoryMaterialPortLedger.environmentStoredFinally r
         + MemoryMaterialPortLedger.localFinallyStored r))))

record RepeatableSourceReceiverCycle : Set where
  constructor repeatableSourceReceiverCycle
  field
    naturalReplenishment driverWork modulationWork : Nat
    usefulWork allDissipationAndRadiation : Nat
    cycleBalance :
      ((naturalReplenishment + driverWork) + modulationWork)
        ≡ usefulWork + allDissipationAndRadiation

repeatableCycleUsefulWorkBound : (r : RepeatableSourceReceiverCycle) →
  Bound._≤_ (RepeatableSourceReceiverCycle.usefulWork r)
    ((RepeatableSourceReceiverCycle.naturalReplenishment r
      + RepeatableSourceReceiverCycle.driverWork r)
      + RepeatableSourceReceiverCycle.modulationWork r)
repeatableCycleUsefulWorkBound r =
  Bound.transportUpper
    (Bound.sym (RepeatableSourceReceiverCycle.cycleBalance r))
    (Bound.≤-append (RepeatableSourceReceiverCycle.usefulWork r)
       (RepeatableSourceReceiverCycle.allDissipationAndRadiation r))

record PassiveFiniteDonor : Set where
  constructor passiveFiniteDonor
  field
    sourceInitiallyStored deliveredToReceiver sourceFinallyStored sourceLoss : Nat
    sourceSideBalance :
      sourceInitiallyStored ≡ deliveredToReceiver
        + (sourceFinallyStored + sourceLoss)

finiteDonorTransferBound : (r : PassiveFiniteDonor) →
  Bound._≤_ (PassiveFiniteDonor.deliveredToReceiver r)
    (PassiveFiniteDonor.sourceInitiallyStored r)
finiteDonorTransferBound r =
  Bound.transportUpper
    (Bound.sym (PassiveFiniteDonor.sourceSideBalance r))
    (Bound.≤-append (PassiveFiniteDonor.deliveredToReceiver r)
       (PassiveFiniteDonor.sourceFinallyStored r
        + PassiveFiniteDonor.sourceLoss r))

-- Explicit physical admission, not derivable from patents or audio alone.
record OriginalDispersiveSourceWeld : Set₁ where
  field
    OriginalEarthAirOrAntennaGeometry : Set
    PhysicalPermittivityPolarizationAndHallPedersen : Set
    LocalPhaseAndWaveformMeasurements : Set
    CausalMaxwellSpatialSourceResponse : Set
    SourceReplenishmentOverRepeatableCycle : Set
    geometry : OriginalEarthAirOrAntennaGeometry
    materials : PhysicalPermittivityPolarizationAndHallPedersen
    phaseTrace : LocalPhaseAndWaveformMeasurements
    fieldSolution : CausalMaxwellSpatialSourceResponse
    replenishmentReceipt : SourceReplenishmentOverRepeatableCycle


------------------------------------------------------------------------
-- 2026-11-16 P2-PHYS: source-ACCESS admission, never source invention.
--
-- A positive-real impedance can support large displacement or memory
-- currents while delivering zero new natural input on a repeatable cycle.
-- The external atmosphere/soil measurement supplies an INDEPENDENT bound
-- before the receiving optimisation may claim physical access.
------------------------------------------------------------------------

record AdmittedNaturalAccessCap : Set where
  constructor admittedNaturalAccessCap
  field
    naturallyDeliveredWork unusedPotentialWork admittedTerminalCap : Nat
    sameSourcePortBound :
      naturallyDeliveredWork + unusedPotentialWork ≡ admittedTerminalCap

naturalWorkCannotExceedMeasuredAccessCap :
  (r : AdmittedNaturalAccessCap) →
  Bound._≤_ (AdmittedNaturalAccessCap.naturallyDeliveredWork r)
            (AdmittedNaturalAccessCap.admittedTerminalCap r)
naturalWorkCannotExceedMeasuredAccessCap r =
  Bound.transportUpper
    (AdmittedNaturalAccessCap.sameSourcePortBound r)
    (Bound.≤-append (AdmittedNaturalAccessCap.naturallyDeliveredWork r)
      (AdmittedNaturalAccessCap.unusedPotentialWork r))

-- Complete-state periodic return: the admitted source CAP includes any
-- inaccessible capacity and cannot be enlarged by mere reactive cycles.
-- This ledger is intentionally stricter than the finite-donor witness.
record TerminalCapRepeatableCycle : Set where
  constructor terminalCapRepeatableCycle
  field
    naturalSourceAccessCap driverWork modulatorWork : Nat
    usefulLoadWork lossesAndRadiation unusedNaturalHeadroom : Nat
    selectedSourceAndSameCycleBalance :
      ((naturalSourceAccessCap + driverWork) + modulatorWork)
        ≡ usefulLoadWork + (lossesAndRadiation + unusedNaturalHeadroom)

loadBelowAdmittedSourcePlusDriveAndModulation :
  (r : TerminalCapRepeatableCycle) →
  Bound._≤_ (TerminalCapRepeatableCycle.usefulLoadWork r)
    ((TerminalCapRepeatableCycle.naturalSourceAccessCap r
        + TerminalCapRepeatableCycle.driverWork r)
        + TerminalCapRepeatableCycle.modulatorWork r)
loadBelowAdmittedSourcePlusDriveAndModulation r =
  Bound.transportUpper
    (Bound.sym (TerminalCapRepeatableCycle.selectedSourceAndSameCycleBalance r))
    (Bound.≤-append (TerminalCapRepeatableCycle.usefulLoadWork r)
      (TerminalCapRepeatableCycle.lossesAndRadiation r
       + TerminalCapRepeatableCycle.unusedNaturalHeadroom r))

-- Constructive NEGATIVE control: internal reactive traffic may be nonzero
-- while the admitted natural work and useful work are both zero.
-- This is not an empirical Hall, soil, or Maxwell measurement.
reactiveTransportWithoutNaturalWork : TerminalCapRepeatableCycle
reactiveTransportWithoutNaturalWork =
  terminalCapRepeatableCycle 0 0 0 0 0 0 refl

-- Physical promotion is still absent. The full original source admittance
-- must be separately calibrated under actual phase and load changes.
record SameOriginalAdmittanceAdmission : Set₁ where
  field
    originalDispersiveWitness : OriginalDispersiveSourceWeld
    SelectedElectrodeAndCollectorGeometry : Set
    MeasuredLocalElectricFieldAndSoilResponse : Set
    IndependentNaturalSourceTheveninOrRetardedOperator : Set
    TimedLoadDriveControllerAndStoredState : Set
    CalibratedRealAndReactivePowers : Set
    chosenGeometry : SelectedElectrodeAndCollectorGeometry
    localFields : MeasuredLocalElectricFieldAndSoilResponse
    sourceOperator : IndependentNaturalSourceTheveninOrRetardedOperator
    synchronousTrace : TimedLoadDriveControllerAndStoredState
    realReactiveReceipt : CalibratedRealAndReactivePowers
