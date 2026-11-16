module DASHI.Physics.Motors.SmithFilsingerReplenishedCycleCapExact where

-- A conditional finite-Nat GRID theorem: after all storage returns,
-- useful work cannot exceed independently admitted NATURAL work plus
-- controller work. If natural source work has a separately admitted cap,
-- useful work is bounded by that cap plus the controller.
--
-- It proves no claims about the original Filsinger apparatus: there is NO
-- measured source operator, Maxwell/plasma solution or actual same-cycle
-- voltage-current record. No equality of arbitrary real-valued energies is
-- inferred from Nat quantisation.
-- Reuses canonical energy Nat order owner instead of duplicating it.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound
import DASHI.Physics.Motors.SmithFilsingerMidpointPhaseWorkExact as Midpoint
import DASHI.Physics.Motors.SmithFilsingerFiniteReservoirPortExact as Reservoir

cong : {A B : Set} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

sucInjective : {x y : Nat} → suc x ≡ suc y → x ≡ y
sucInjective refl = refl

+-assoc : (a b c : Nat) → (a + b) + c ≡ a + (b + c)
+-assoc zero b c = refl
+-assoc (suc a) b c rewrite +-assoc a b c = refl

+-zeroRight : (a : Nat) → a + zero ≡ a
+-zeroRight zero = refl
+-zeroRight (suc a) rewrite +-zeroRight a = refl

+-sucRight : (a b : Nat) → a + suc b ≡ suc (a + b)
+-sucRight zero b = refl
+-sucRight (suc a) b rewrite +-sucRight a b = refl

+-comm : (a b : Nat) → a + b ≡ b + a
+-comm zero b rewrite +-zeroRight b = refl
+-comm (suc a) b rewrite +-comm a b | +-sucRight b a = refl

+-cancelLeft : (z a b : Nat) → z + a ≡ z + b → a ≡ b
+-cancelLeft zero a b eq = eq
+-cancelLeft (suc z) a b eq =
  +-cancelLeft z a b (sucInjective eq)

+-cancelRight : (a b z : Nat) → a + z ≡ b + z → a ≡ b
+-cancelRight a b z eq =
  +-cancelLeft z a b
    (trans (+-comm z a) (trans eq (Bound.sym (+-comm z b))))

≤-trans : {a b c : Nat} → Bound._≤_ a b → Bound._≤_ b c → Bound._≤_ a c
≤-trans Bound.z≤n _ = Bound.z≤n
≤-trans (Bound.s≤s p) (Bound.s≤s q) = Bound.s≤s (≤-trans p q)

+-monotoneRight : {a b : Nat} (c : Nat) →
  Bound._≤_ a b → Bound._≤_ (a + c) (b + c)
+-monotoneRight {b = b} c Bound.z≤n =
  Bound.transportUpper (+-comm c b) (Bound.≤-append c b)
+-monotoneRight c (Bound.s≤s p) =
  Bound.s≤s (+-monotoneRight c p)

record RepeatableSourceCycle : Set where
  constructor repeatableSourceCycle
  field
    naturalSourceWork controllerWork : Nat
    initialAllStorage finalAllStorage : Nat
    usefulLoadWork allHeatAndOutgoing : Nat
    wholeBoundaryLaw :
      (naturalSourceWork + controllerWork) + initialAllStorage
        ≡ usefulLoadWork + (allHeatAndOutgoing + finalAllStorage)
    everyStoreRestored : initialAllStorage ≡ finalAllStorage

-- The strict same-cycle boundary ledger excludes one-time donor drawdown.
workPaidAfterStorageReturns : (r : RepeatableSourceCycle) →
  RepeatableSourceCycle.naturalSourceWork r +
    RepeatableSourceCycle.controllerWork r
    ≡ RepeatableSourceCycle.usefulLoadWork r +
      RepeatableSourceCycle.allHeatAndOutgoing r
workPaidAfterStorageReturns r =
  +-cancelRight _ _ (RepeatableSourceCycle.finalAllStorage r)
    (trans
      (cong (λ z →
        (RepeatableSourceCycle.naturalSourceWork r +
          RepeatableSourceCycle.controllerWork r) + z)
        (Bound.sym (RepeatableSourceCycle.everyStoreRestored r)))
      (trans (RepeatableSourceCycle.wholeBoundaryLaw r)
        (Bound.sym (+-assoc
          (RepeatableSourceCycle.usefulLoadWork r)
          (RepeatableSourceCycle.allHeatAndOutgoing r)
          (RepeatableSourceCycle.finalAllStorage r)))))

loadBoundByReplenishmentAndController : (r : RepeatableSourceCycle) →
  Bound._≤_ (RepeatableSourceCycle.usefulLoadWork r)
    (RepeatableSourceCycle.naturalSourceWork r +
      RepeatableSourceCycle.controllerWork r)
loadBoundByReplenishmentAndController r =
  Bound.transportUpper (Bound.sym (workPaidAfterStorageReturns r))
    (Bound.≤-append
      (RepeatableSourceCycle.usefulLoadWork r)
      (RepeatableSourceCycle.allHeatAndOutgoing r))

record AdmittedSourceCapCycle : Set where
  constructor admittedSourceCapCycle
  field
    repeatable : RepeatableSourceCycle
    independentlyAdmittedNaturalCap unspentNaturalBudget : Nat
    capReceipt :
      RepeatableSourceCycle.naturalSourceWork repeatable +
        unspentNaturalBudget ≡ independentlyAdmittedNaturalCap

naturalInputUnderAdmittedCap : (r : AdmittedSourceCapCycle) →
  Bound._≤_ (RepeatableSourceCycle.naturalSourceWork
              (AdmittedSourceCapCycle.repeatable r))
    (AdmittedSourceCapCycle.independentlyAdmittedNaturalCap r)
naturalInputUnderAdmittedCap r =
  Bound.transportUpper (AdmittedSourceCapCycle.capReceipt r)
    (Bound.≤-append
      (RepeatableSourceCycle.naturalSourceWork
        (AdmittedSourceCapCycle.repeatable r))
      (AdmittedSourceCapCycle.unspentNaturalBudget r))

-- Critical max cut: independently established SOURCE ACCESS bounds the
-- useful work over a repeatable cycle, irrespective of *internal* phase.
replenishedLoadBelowNaturalCapPlusController :
  (r : AdmittedSourceCapCycle) →
  Bound._≤_ (RepeatableSourceCycle.usefulLoadWork
              (AdmittedSourceCapCycle.repeatable r))
    (AdmittedSourceCapCycle.independentlyAdmittedNaturalCap r +
      RepeatableSourceCycle.controllerWork
        (AdmittedSourceCapCycle.repeatable r))
replenishedLoadBelowNaturalCapPlusController r =
  ≤-trans
    (loadBoundByReplenishmentAndController
      (AdmittedSourceCapCycle.repeatable r))
    (+-monotoneRight
      (RepeatableSourceCycle.controllerWork
        (AdmittedSourceCapCycle.repeatable r))
      (naturalInputUnderAdmittedCap r))

-- A concrete finite renewable-source witness: 3+1=2+2, all stores 5.
-- This proves only logical consistency, not naturally available watts.
modelCycleWitness : RepeatableSourceCycle
modelCycleWitness = repeatableSourceCycle 3 1 5 5 2 2 refl refl

modelCycleWorkPaid :
  RepeatableSourceCycle.naturalSourceWork modelCycleWitness +
    RepeatableSourceCycle.controllerWork modelCycleWitness
   ≡ RepeatableSourceCycle.usefulLoadWork modelCycleWitness +
      RepeatableSourceCycle.allHeatAndOutgoing modelCycleWitness
modelCycleWorkPaid = workPaidAfterStorageReturns modelCycleWitness

modelAdmittedCapWitness : AdmittedSourceCapCycle
modelAdmittedCapWitness = admittedSourceCapCycle modelCycleWitness 5 2 refl

modelCapBound :
  Bound._≤_ (RepeatableSourceCycle.usefulLoadWork modelCycleWitness)
    (AdmittedSourceCapCycle.independentlyAdmittedNaturalCap
       modelAdmittedCapWitness +
     RepeatableSourceCycle.controllerWork modelCycleWitness)
modelCapBound =
  replenishedLoadBelowNaturalCapPlusController modelAdmittedCapWitness

-- These evidence requirements are NOT inhabited. No electromagnetic, weather,
-- original-plate or original-Earth-source proof is smuggled into Set fields.
record SameOriginalCycleAdmission : Set₁ where
  field
    sourceRegime : Midpoint.EnvironmentalSourceRegime
    sourceAndDriverBoundary : Reservoir.SameOriginalEnvironmentalAdmission
    SelectedPinsAndFullGroundReturns : Set
    OriginalSynchronousSourceDriverControllerLoadCurrents : Set
    IndependentlyCalibratedSourceAdmittanceAndAccessibleWork : Set
    SourceReplenishmentAndEveryStorageReturn : Set
    CalibratedFullCausalMaxwellMaterialSolution : Set
    pins : SelectedPinsAndFullGroundReturns
    workTrace : OriginalSynchronousSourceDriverControllerLoadCurrents
    sourceOperator : IndependentlyCalibratedSourceAdmittanceAndAccessibleWork
    replenishmentReceipt : SourceReplenishmentAndEveryStorageReturn
    fieldWeld : CalibratedFullCausalMaxwellMaterialSolution
