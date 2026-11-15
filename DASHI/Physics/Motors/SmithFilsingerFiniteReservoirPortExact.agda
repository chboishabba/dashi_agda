module DASHI.Physics.Motors.SmithFilsingerFiniteReservoirPortExact where

-- Original source-qualified conditional finite reservoir accounting.
-- Not evidence that Filsinger's apparatus extracts atmospheric power.
-- Local full math & original-model replay: smith_filsinger_reservoir_maxcut_20261115.zip

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound

record CoupledNaturalReservoirReceipt : Set where
  constructor coupledNaturalReservoirReceipt
  field
    driverWork controllerWork naturalRecharge : Nat
    localInitiallyStored environmentInitiallyStored : Nat
    usefulLoadWork dissipatedOrReradiated : Nat
    localFinallyStored environmentFinallyStored : Nat
    allPortBoundaryBalance :
      ((driverWork + controllerWork) + naturalRecharge)
        + (localInitiallyStored + environmentInitiallyStored)
      ≡ usefulLoadWork
        + (dissipatedOrReradiated +
            (localFinallyStored + environmentFinallyStored))

availableFromAllSourcePorts : CoupledNaturalReservoirReceipt → Nat
availableFromAllSourcePorts r =
  ((CoupledNaturalReservoirReceipt.driverWork r
    + CoupledNaturalReservoirReceipt.controllerWork r)
    + CoupledNaturalReservoirReceipt.naturalRecharge r)
   + (CoupledNaturalReservoirReceipt.localInitiallyStored r
      + CoupledNaturalReservoirReceipt.environmentInitiallyStored r)

usefulLoadBoundedByDriverReservoirAndController :
  (r : CoupledNaturalReservoirReceipt) →
  Bound._≤_ (CoupledNaturalReservoirReceipt.usefulLoadWork r)
            (availableFromAllSourcePorts r)
usefulLoadBoundedByDriverReservoirAndController r =
  Bound.transportUpper
    (Bound.sym (CoupledNaturalReservoirReceipt.allPortBoundaryBalance r))
    (Bound.≤-append
      (CoupledNaturalReservoirReceipt.usefulLoadWork r)
      (CoupledNaturalReservoirReceipt.dissipatedOrReradiated r
       + (CoupledNaturalReservoirReceipt.localFinallyStored r
        + CoupledNaturalReservoirReceipt.environmentFinallyStored r)))

record NaturalReservoirDonorReceipt : Set where
  constructor naturalReservoirDonorReceipt
  field
    environmentInitiallyStored environmentFinallyStored : Nat
    naturalRecharge environmentHeatAndRadiation : Nat
    transferredToOtherMembers : Nat
    sourceSideBoundaryBalance :
      transferredToOtherMembers
        + (environmentFinallyStored + environmentHeatAndRadiation)
      ≡ environmentInitiallyStored + naturalRecharge

transferNoGreaterThanSourceStorageAndRecharge :
  (r : NaturalReservoirDonorReceipt) →
  Bound._≤_ (NaturalReservoirDonorReceipt.transferredToOtherMembers r)
            (NaturalReservoirDonorReceipt.environmentInitiallyStored r
             + NaturalReservoirDonorReceipt.naturalRecharge r)
transferNoGreaterThanSourceStorageAndRecharge r =
  Bound.transportUpper
    (NaturalReservoirDonorReceipt.sourceSideBoundaryBalance r)
    (Bound.≤-append
      (NaturalReservoirDonorReceipt.transferredToOtherMembers r)
      (NaturalReservoirDonorReceipt.environmentFinallyStored r
       + NaturalReservoirDonorReceipt.environmentHeatAndRadiation r))

record DriverPlusControllerOnly : Set where
  constructor driverPlusControllerOnly
  field
    driverWork controllerWork usefulLoadWork lossesAndFinalStored : Nat
    allPortBoundaryBalance :
      driverWork + controllerWork ≡ usefulLoadWork + lossesAndFinalStored

driverAndControllerOnlyBound : (r : DriverPlusControllerOnly) →
  Bound._≤_ (DriverPlusControllerOnly.usefulLoadWork r)
      (DriverPlusControllerOnly.driverWork r
       + DriverPlusControllerOnly.controllerWork r)
driverAndControllerOnlyBound r =
  Bound.transportUpper
    (Bound.sym (DriverPlusControllerOnly.allPortBoundaryBalance r))
    (Bound.≤-append (DriverPlusControllerOnly.usefulLoadWork r)
                    (DriverPlusControllerOnly.lossesAndFinalStored r))

-- Algebraic possibility witness (not hardware): a smaller controller can
-- transfer energy from a larger stored donor. 1+1+20=4+18.
finiteReservoirCanOutdeliverSmallDriver : CoupledNaturalReservoirReceipt
finiteReservoirCanOutdeliverSmallDriver =
  coupledNaturalReservoirReceipt 1 1 0 0 20 4 0 0 18 refl

finiteReservoirWitnessBound :
  Bound._≤_ (CoupledNaturalReservoirReceipt.usefulLoadWork
              finiteReservoirCanOutdeliverSmallDriver)
             (availableFromAllSourcePorts finiteReservoirCanOutdeliverSmallDriver)
finiteReservoirWitnessBound =
  usefulLoadBoundedByDriverReservoirAndController
    finiteReservoirCanOutdeliverSmallDriver

-- Physical promotion gate: papers, patents, audio and toy simulations
-- do not supply these same-apparatus receipts.
record SameOriginalEnvironmentalAdmission : Set₁ where
  field
    SelectedFilsingerEarthOrAntennaPins : Set
    RetardedSourceToReceiverMaxwellSolution : Set
    SelectedNonlinearMaterialAndFieldLaw : Set
    MeasuredSourcePortElectricalClock : Set
    IndependentEnvironmentReplenishmentReceipt : Set
    SameApparatusSignedRealWork : Set
    actualPins : SelectedFilsingerEarthOrAntennaPins
    sourceField : RetardedSourceToReceiverMaxwellSolution
    materialWeld : SelectedNonlinearMaterialAndFieldLaw
    electricalTrace : MeasuredSourcePortElectricalClock
    independentSource : IndependentEnvironmentReplenishmentReceipt
    physicalWorkReceipt : SameApparatusSignedRealWork
