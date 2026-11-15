module DASHI.Physics.Motors.SmithFilsingerShuntAndSourceAccessExact where

-- Original DASHI finite Nat-grid work and source-observation contracts.
-- Physical V²/R and Thevenin maximum power are proven symbolically in
-- Python, not postulated as real-number theorems in this Nat module.
-- Three 1MΩ shunts simultaneously at 1500V DC is a *conditional* scenario.

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound

record TimedShuntWorkReceipt : Set where
  constructor timedShuntWorkReceipt
  field
    driverInput naturalSourceInput storageDepletion : Nat
    dissipatedInKnownShunts otherLosses finalUnallocatedEnergy : Nat
    fullSourceBudget :
      (driverInput + naturalSourceInput) + storageDepletion
        ≡ dissipatedInKnownShunts + (otherLosses + finalUnallocatedEnergy)

shuntWorkNoGreaterThanAllInputs : (r : TimedShuntWorkReceipt) →
  Bound._≤_ (TimedShuntWorkReceipt.dissipatedInKnownShunts r)
    ((TimedShuntWorkReceipt.driverInput r
      + TimedShuntWorkReceipt.naturalSourceInput r)
       + TimedShuntWorkReceipt.storageDepletion r)
shuntWorkNoGreaterThanAllInputs r =
  Bound.transportUpper
    (Bound.sym (TimedShuntWorkReceipt.fullSourceBudget r))
    (Bound.≤-append (TimedShuntWorkReceipt.dissipatedInKnownShunts r)
      (TimedShuntWorkReceipt.otherLosses r
        + TimedShuntWorkReceipt.finalUnallocatedEnergy r))

-- Units: hundredths of watt, under stated steady, simultaneous assumptions.
sourceAssumedSingleShuntCentWatts : Nat
sourceAssumedSingleShuntCentWatts = 225

sourceAssumedThreeShuntsCentWatts : Nat
sourceAssumedThreeShuntsCentWatts =
  sourceAssumedSingleShuntCentWatts
    + (sourceAssumedSingleShuntCentWatts
      + sourceAssumedSingleShuntCentWatts)

hypotheticalThreeAt1500VIdentity :
  sourceAssumedThreeShuntsCentWatts ≡ 675
hypotheticalThreeAt1500VIdentity = refl

data Empty : Set where

-- This excludes ONLY the all-drive, no-reserve/no-extra-source reference
-- equation 670=675, not an actual Filsinger physical measurement.
noDriveOnly670Equals675 : 670 ≡ 675 → Empty
noDriveOnly670Equals675 ()

data PhysicalWorld : Set where
  internallyCharged naturallyAssisted : PhysicalWorld

data CapacitorVoltageObservation : Set where
  sameNominal1500V : CapacitorVoltageObservation

meterObservation : PhysicalWorld → CapacitorVoltageObservation
meterObservation internallyCharged = sameNominal1500V
meterObservation naturallyAssisted = sameNominal1500V

data NaturalInputClass : Set where
  absent present : NaturalInputClass

naturalPort : PhysicalWorld → NaturalInputClass
naturalPort internallyCharged = absent
naturalPort naturallyAssisted = present

absentIsNotPresent : absent ≡ present → Empty
absentIsNotPresent ()

MeterAloneDeterminesNaturalInput : Set
MeterAloneDeterminesNaturalInput =
  (a b : PhysicalWorld) →
    meterObservation a ≡ meterObservation b → naturalPort a ≡ naturalPort b

meterAloneCannotDetermineNaturalInput :
  MeterAloneDeterminesNaturalInput → Empty
meterAloneCannotDetermineNaturalInput f =
  absentIsNotPresent (f internallyCharged naturallyAssisted refl)

data SourceOperator : Set where
  fixedPositiveResistanceSource nonlinearRetardedSource : SourceOperator

record ActualSourcePortAdmission : Set₁ where
  field
    OriginalShuntTerminalContinuity : Set
    SimultaneousShuntVoltagesAndCurrents : Set
    OriginalSourceOpenAndLoadedElectricalPairs : Set
    StableTheveninOrRetardedSourceModel : Set
    SameCycleDriverNaturalAndStorageWork : Set
    selectedPins : OriginalShuntTerminalContinuity
    synchronisedTrace : SimultaneousShuntVoltagesAndCurrents
    loadedSourcePairs : OriginalSourceOpenAndLoadedElectricalPairs
    sourceLaw : StableTheveninOrRetardedSourceModel
    sourceWork : SameCycleDriverNaturalAndStorageWork
