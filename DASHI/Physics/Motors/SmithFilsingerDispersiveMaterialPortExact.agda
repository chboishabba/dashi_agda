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
