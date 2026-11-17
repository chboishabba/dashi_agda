module DASHI.Physics.Motors.SmithFilsingerDispersiveMaterialWeldExact where

-- WELD TO THE ORIGINAL #1521 MATERIAL SOURCE, NOT A NEW SIMULATOR.
-- SmithFilsingerDispersiveMaterialPortExact.agda was copied into this
-- branch as the EXACT byte-identical upstream Git blob for import reuse.
-- Do not edit or fork that donor: extend it here.
--
-- Poynting and nonlinear polarization/material energy are independent
-- physical admissions. This module proves from the donor's ACTUAL
-- fullBalance, rather than declaring another aggregate law, what happens
-- when all source/material states return.
-- Source: user-origin Smith/Filsinger mechanism; exact earlier DASHI
-- source owners. No actual Earth/solar current or rain claim is admitted.

open import Agda.Builtin.Nat using (Nat; zero; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:=_)

import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound
import DASHI.Physics.Motors.SmithFilsingerReplenishedCycleCapExact as Cycle
import DASHI.Physics.Motors.SmithFilsingerDispersiveMaterialPortExact as Mat
import DASHI.Physics.Motors.SmithFilsingerMaxwellMaterialEnergyCutExact as Cut
import DASHI.Physics.Motors.SmithFilsingerSourceMaxwellBoundaryWeldExact as Weld
import DASHI.Physics.Motors.SmithFilsingerMidpointPhaseWorkExact as Port

-- Match the original #1521 stored field/environment and local material
-- energies. Cancellation is exact only if BOTH inventories return.
donorAllStoresReturn :
  (r : Mat.MemoryMaterialPortLedger) →
  Mat.MemoryMaterialPortLedger.environmentStoredInitially r
    ≡ Mat.MemoryMaterialPortLedger.environmentStoredFinally r →
  Mat.MemoryMaterialPortLedger.localInitiallyStored r
    ≡ Mat.MemoryMaterialPortLedger.localFinallyStored r →
  (Mat.MemoryMaterialPortLedger.environmentStoredInitially r
    + Mat.MemoryMaterialPortLedger.localInitiallyStored r)
  ≡ (Mat.MemoryMaterialPortLedger.environmentStoredFinally r
    + Mat.MemoryMaterialPortLedger.localFinallyStored r)
donorAllStoresReturn r env local =
  Cycle.trans
    (Cycle.cong
      (λ z → z + Mat.MemoryMaterialPortLedger.localInitiallyStored r) env)
    (Cycle.cong
      (λ z → Mat.MemoryMaterialPortLedger.environmentStoredFinally r + z) local)

-- Re-normalise the ORIGINAL #1521 balance around the combined stores.
donorReorderInputs :
  (environmentInitial natural driver modulation localInitial : Nat) →
  (((environmentInitial + natural) + driver) + (modulation + localInitial))
    ≡ ((natural + driver) + modulation) + (environmentInitial + localInitial)
donorReorderInputs ei n d m li =
  solve 5
    (λ e s p q l →
      (((e :+ s) :+ p) :+ (q :+ l))
      := (((s :+ p) :+ q) :+ (e :+ l)))
    refl ei n d m li

donorReorderOutputs :
  (load resistive feed recovery environmentFinal localFinal : Nat) →
  load + ((resistive + feed) + (recovery + (environmentFinal + localFinal)))
    ≡ (load + (resistive + (feed + recovery)))
        + (environmentFinal + localFinal)
donorReorderOutputs load resistive feed recovery ef lf =
  solve 6
    (λ l r f m e q →
      (l :+ ((r :+ f) :+ (m :+ (e :+ q))))
      := ((l :+ (r :+ (f :+ m))) :+ (e :+ q)))
    refl load resistive feed recovery ef lf

-- Strong F15 ORIGINAL producer theorem, not a new accepted energy axiom:
-- exactly the #1521 MemoryMaterialPortLedger.fullBalance gives this
-- once both environment and receiver material storage return.
originalDispersiveRepeatableWork :
  (r : Mat.MemoryMaterialPortLedger) →
  Mat.MemoryMaterialPortLedger.environmentStoredInitially r
    ≡ Mat.MemoryMaterialPortLedger.environmentStoredFinally r →
  Mat.MemoryMaterialPortLedger.localInitiallyStored r
    ≡ Mat.MemoryMaterialPortLedger.localFinallyStored r →
  ((Mat.MemoryMaterialPortLedger.environmentRecharged r
     + Mat.MemoryMaterialPortLedger.driverWork r)
    + Mat.MemoryMaterialPortLedger.materialModulatorInput r)
  ≡ Mat.MemoryMaterialPortLedger.usefulWork r
    + (Mat.MemoryMaterialPortLedger.resistiveAndRelaxationLoss r
      + (Mat.MemoryMaterialPortLedger.feedLoss r
        + Mat.MemoryMaterialPortLedger.materialModulatorRecovery r))
originalDispersiveRepeatableWork r env local =
  Cycle.+-cancelRight _ _ storedFinal
    (Cycle.trans
      (Cycle.cong (λ z → totalInput + z)
        (Bound.sym (donorAllStoresReturn r env local)))
      (Cycle.trans
        (Bound.sym (donorReorderInputs
          ei n d m li))
        (Cycle.trans
          (Mat.MemoryMaterialPortLedger.fullBalance r)
          (donorReorderOutputs load resistive feed recover ef lf))))
  where
    open Mat.MemoryMaterialPortLedger r renaming
      (environmentStoredInitially to ei;
       environmentStoredFinally to ef;
       environmentRecharged to n;
       driverWork to d;
       materialModulatorInput to m;
       localInitiallyStored to li;
       localFinallyStored to lf;
       usefulWork to load;
       resistiveAndRelaxationLoss to resistive;
       feedLoss to feed;
       materialModulatorRecovery to recover)
    totalInput : Nat
    totalInput = (n + d) + m
    storedFinal : Nat
    storedFinal = ef + lf

originalDispersiveLoadBound :
  (r : Mat.MemoryMaterialPortLedger) →
  Mat.MemoryMaterialPortLedger.environmentStoredInitially r
    ≡ Mat.MemoryMaterialPortLedger.environmentStoredFinally r →
  Mat.MemoryMaterialPortLedger.localInitiallyStored r
    ≡ Mat.MemoryMaterialPortLedger.localFinallyStored r →
  Bound._≤_
    (Mat.MemoryMaterialPortLedger.usefulWork r)
    ((Mat.MemoryMaterialPortLedger.environmentRecharged r
      + Mat.MemoryMaterialPortLedger.driverWork r)
       + Mat.MemoryMaterialPortLedger.materialModulatorInput r)
originalDispersiveLoadBound r env local =
  Bound.transportUpper
    (Bound.sym (originalDispersiveRepeatableWork r env local))
    (Bound.≤-append
      (Mat.MemoryMaterialPortLedger.usefulWork r)
      (Mat.MemoryMaterialPortLedger.resistiveAndRelaxationLoss r
        + (Mat.MemoryMaterialPortLedger.feedLoss r
          + Mat.MemoryMaterialPortLedger.materialModulatorRecovery r)))

-- Actual same-original cross-PR weld: the canonical donor #1521 ledger
-- and the new field/material split refer to IDENTICAL original energy
-- ports, not just arbitrary numbers in different experimental worlds.
record CanonicalDispersiveSameObject
  (b : Weld.SelectedBoundary)
  (f : Weld.FormalFieldToPort b)
  (s : Weld.SignedSourceCycleWeld b f)
  (w : Cut.FieldMaterialEnergyWeld b f s) : Set₂ where
  field
    canonicalDonor : Mat.MemoryMaterialPortLedger
    originalAdmittanceEvidence : Mat.SameOriginalAdmittanceAdmission

    donorNaturalIsNetOriginal :
      Mat.MemoryMaterialPortLedger.environmentRecharged canonicalDonor
        ≡ Cut.FieldMaterialEnergyWeld.naturalInput w
    donorDriverIsNetOriginal :
      Mat.MemoryMaterialPortLedger.driverWork canonicalDonor
        ≡ Cut.FieldMaterialEnergyWeld.driverInput w
    donorMaterialModulationMatches :
      Mat.MemoryMaterialPortLedger.materialModulatorInput canonicalDonor
        ≡ Cut.FieldMaterialEnergyWeld.modulationInput w
    donorMaterialRecoveryMatches :
      Mat.MemoryMaterialPortLedger.materialModulatorRecovery canonicalDonor
        ≡ Cut.FieldMaterialEnergyWeld.modulationRecovery w
    donorUsefulLoadIsOriginal :
      Mat.MemoryMaterialPortLedger.usefulWork canonicalDonor
        ≡ Cut.FieldMaterialEnergyWeld.usefulLoad w
    donorDissipationMatchesFieldMaterial :
      Mat.MemoryMaterialPortLedger.resistiveAndRelaxationLoss canonicalDonor
        + Mat.MemoryMaterialPortLedger.feedLoss canonicalDonor
        ≡ Cut.FieldMaterialEnergyWeld.fieldDissipationAndOutgoing w
          + Cut.FieldMaterialEnergyWeld.materialDissipation w
    donorInitialEnvironmentMatchesField :
      Mat.MemoryMaterialPortLedger.environmentStoredInitially canonicalDonor
        ≡ Cut.FieldMaterialEnergyWeld.fieldStoredInitially w
    donorFinalEnvironmentMatchesField :
      Mat.MemoryMaterialPortLedger.environmentStoredFinally canonicalDonor
        ≡ Cut.FieldMaterialEnergyWeld.fieldStoredFinally w
    donorInitialLocalMatchesMaterial :
      Mat.MemoryMaterialPortLedger.localInitiallyStored canonicalDonor
        ≡ Cut.FieldMaterialEnergyWeld.materialStoredInitially w
    donorFinalLocalMatchesMaterial :
      Mat.MemoryMaterialPortLedger.localFinallyStored canonicalDonor
        ≡ Cut.FieldMaterialEnergyWeld.materialStoredFinally w
    donorEnvironmentalStorageReturns :
      Mat.MemoryMaterialPortLedger.environmentStoredInitially canonicalDonor
        ≡ Mat.MemoryMaterialPortLedger.environmentStoredFinally canonicalDonor
    donorMaterialStorageReturns :
      Mat.MemoryMaterialPortLedger.localInitiallyStored canonicalDonor
        ≡ Mat.MemoryMaterialPortLedger.localFinallyStored canonicalDonor

-- The exact original donor ledger now proves the same bounded load as
-- the new source-selected receiver; driver + modulation remain paid.
-- Not derived from measured material response: same-object evidence is
-- a separate required witness, and no original value is constructed.
donorOriginalLoadIsPaid :
  (b : Weld.SelectedBoundary)
  (f : Weld.FormalFieldToPort b)
  (s : Weld.SignedSourceCycleWeld b f)
  (w : Cut.FieldMaterialEnergyWeld b f s)
  (x : CanonicalDispersiveSameObject b f s w) →
  Bound._≤_
    (Port.MidpointTwoPortWorkWindow.usefulWork
      (Weld.FormalFieldToPort.portWindow f))
    ((Cut.FieldMaterialEnergyWeld.naturalInput w
      + Cut.FieldMaterialEnergyWeld.driverInput w)
      + Cut.FieldMaterialEnergyWeld.modulationInput w)
donorOriginalLoadIsPaid b f s w x =
  substLower
    (Bound.sym (Cycle.trans
      (CanonicalDispersiveSameObject.donorUsefulLoadIsOriginal x)
      (Cut.FieldMaterialEnergyWeld.sameOriginalLoad w)))
    (Bound.transportUpper
      totalInputEqual
      (originalDispersiveLoadBound donor
        (CanonicalDispersiveSameObject.donorEnvironmentalStorageReturns x)
        (CanonicalDispersiveSameObject.donorMaterialStorageReturns x)))
  where
    substLower : {a b c : Nat} →
      a ≡ b → Bound._≤_ b c → Bound._≤_ a c
    substLower refl p = p

    donor : Mat.MemoryMaterialPortLedger
    donor = CanonicalDispersiveSameObject.canonicalDonor x

    totalInputEqual :
      ((Mat.MemoryMaterialPortLedger.environmentRecharged donor
        + Mat.MemoryMaterialPortLedger.driverWork donor)
        + Mat.MemoryMaterialPortLedger.materialModulatorInput donor)
      ≡ ((Cut.FieldMaterialEnergyWeld.naturalInput w
        + Cut.FieldMaterialEnergyWeld.driverInput w)
        + Cut.FieldMaterialEnergyWeld.modulationInput w)
    totalInputEqual =
      Cycle.trans
        (Cycle.cong (λ t → t + Mat.MemoryMaterialPortLedger.materialModulatorInput donor)
          (Cycle.trans
            (Cycle.cong
              (λ z → z + Mat.MemoryMaterialPortLedger.driverWork donor)
              (CanonicalDispersiveSameObject.donorNaturalIsNetOriginal x))
            (Cycle.cong
              (λ z → Cut.FieldMaterialEnergyWeld.naturalInput w + z)
              (CanonicalDispersiveSameObject.donorDriverIsNetOriginal x))))
        (Cycle.cong (λ t → (Cut.FieldMaterialEnergyWeld.naturalInput w
              + Cut.FieldMaterialEnergyWeld.driverInput w) + t)
          (CanonicalDispersiveSameObject.donorMaterialModulationMatches x))


-- A genuine cross-owner result: take the ORIGINAL #1521 material full
-- balance with both stores returned, identify exactly the SAME original
-- source/controller/load via the #1524 field weld, and then promote the
-- independent natural access cap. Modulator cost remains a paid input.
donorOriginalLoadBelowAdmittedNaturalCap :
  (b : Weld.SelectedBoundary)
  (f : Weld.FormalFieldToPort b)
  (s : Weld.SignedSourceCycleWeld b f)
  (w : Cut.FieldMaterialEnergyWeld b f s)
  (x : CanonicalDispersiveSameObject b f s w) →
  Bound._≤_
    (Port.MidpointTwoPortWorkWindow.usefulWork
      (Weld.FormalFieldToPort.portWindow f))
    ((Cycle.AdmittedSourceCapCycle.independentlyAdmittedNaturalCap
       (Weld.SignedSourceCycleWeld.cycleWithSourceCap s)
       + Cycle.RepeatableSourceCycle.controllerWork
          (Cycle.AdmittedSourceCapCycle.repeatable
            (Weld.SignedSourceCycleWeld.cycleWithSourceCap s)))
      + Cut.FieldMaterialEnergyWeld.modulationInput w)
donorOriginalLoadBelowAdmittedNaturalCap b f s w x =
  Cycle.≤-trans
    (donorOriginalLoadIsPaid b f s w x)
    (Bound.transportUpper
      driverAndControllerMatch
      (Cycle.+-monotoneRight (Cut.FieldMaterialEnergyWeld.modulationInput w)
        (Cycle.+-monotoneRight (Cut.FieldMaterialEnergyWeld.driverInput w)
          (Cut.netNaturalUnderExistingAdmittedCap b f s w))))
  where
    sourceCap : Nat
    sourceCap =
      Cycle.AdmittedSourceCapCycle.independentlyAdmittedNaturalCap
        (Weld.SignedSourceCycleWeld.cycleWithSourceCap s)
    driverAndControllerMatch :
      ((sourceCap + Cut.FieldMaterialEnergyWeld.driverInput w)
        + Cut.FieldMaterialEnergyWeld.modulationInput w)
      ≡ ((sourceCap
        + Cycle.RepeatableSourceCycle.controllerWork
          (Cycle.AdmittedSourceCapCycle.repeatable
            (Weld.SignedSourceCycleWeld.cycleWithSourceCap s)))
         + Cut.FieldMaterialEnergyWeld.modulationInput w)
    driverAndControllerMatch =
      Cycle.cong
        (λ z → (sourceCap + z) + Cut.FieldMaterialEnergyWeld.modulationInput w)
        (Cut.FieldMaterialEnergyWeld.sameNetPoweredWork w)


-- Original #1521 proof that BOTH environmental and local material stores
-- return now transports through exactly matching #1524 Maxwell/material
-- inventories. This is a true same-object bridge: no independently
-- invented "split storage returns" witness is needed.
donorStorageReturnTransfersToSplit :
  (b : Weld.SelectedBoundary)
  (f : Weld.FormalFieldToPort b)
  (s : Weld.SignedSourceCycleWeld b f)
  (w : Cut.FieldMaterialEnergyWeld b f s)
  (x : CanonicalDispersiveSameObject b f s w) →
  Cut.FieldMaterialEnergyWeld.fieldStoredInitially w
    + Cut.FieldMaterialEnergyWeld.materialStoredInitially w
  ≡ Cut.FieldMaterialEnergyWeld.fieldStoredFinally w
    + Cut.FieldMaterialEnergyWeld.materialStoredFinally w
donorStorageReturnTransfersToSplit b f s w x =
  Cycle.trans
    (Cycle.cong
      (λ z → z + Cut.FieldMaterialEnergyWeld.materialStoredInitially w)
      fieldStoreReturns)
    (Cycle.cong
      (λ z → Cut.FieldMaterialEnergyWeld.fieldStoredFinally w + z)
      materialStoreReturns)
  where
    fieldStoreReturns :
      Cut.FieldMaterialEnergyWeld.fieldStoredInitially w
        ≡ Cut.FieldMaterialEnergyWeld.fieldStoredFinally w
    fieldStoreReturns =
      Cycle.trans
        (Bound.sym (CanonicalDispersiveSameObject.donorInitialEnvironmentMatchesField x))
        (Cycle.trans
          (CanonicalDispersiveSameObject.donorEnvironmentalStorageReturns x)
          (CanonicalDispersiveSameObject.donorFinalEnvironmentMatchesField x))

    materialStoreReturns :
      Cut.FieldMaterialEnergyWeld.materialStoredInitially w
        ≡ Cut.FieldMaterialEnergyWeld.materialStoredFinally w
    materialStoreReturns =
      Cycle.trans
        (Bound.sym (CanonicalDispersiveSameObject.donorInitialLocalMatchesMaterial x))
        (Cycle.trans
          (CanonicalDispersiveSameObject.donorMaterialStorageReturns x)
          (CanonicalDispersiveSameObject.donorFinalLocalMatchesMaterial x))

-- Direct #1521 donor -> #1524 two-law Maxwell/material cap theorem,
-- with NO second independent restoration assumption.
canonicalDispersiveFieldLoadBelowNaturalCap :
  (b : Weld.SelectedBoundary)
  (f : Weld.FormalFieldToPort b)
  (s : Weld.SignedSourceCycleWeld b f)
  (w : Cut.FieldMaterialEnergyWeld b f s)
  (x : CanonicalDispersiveSameObject b f s w) →
  Bound._≤_
    (Port.MidpointTwoPortWorkWindow.usefulWork
      (Weld.FormalFieldToPort.portWindow f))
    ((Cycle.AdmittedSourceCapCycle.independentlyAdmittedNaturalCap
       (Weld.SignedSourceCycleWeld.cycleWithSourceCap s)
       + Cycle.RepeatableSourceCycle.controllerWork
          (Cycle.AdmittedSourceCapCycle.repeatable
            (Weld.SignedSourceCycleWeld.cycleWithSourceCap s)))
       + Cut.FieldMaterialEnergyWeld.modulationInput w)
canonicalDispersiveFieldLoadBelowNaturalCap b f s w x =
  Cut.sameOriginalMaterialCapWithControllerAndModulator b f s w
    (donorStorageReturnTransfersToSplit b f s w x)
