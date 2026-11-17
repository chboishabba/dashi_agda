module DASHI.Physics.Motors.SmithFilsingerHundredfoldSourceFundingExact where

-- F15 mathematical certificate for a 100x *conditional* restored cycle.
-- Reuses canonical repeatable source work theorem; does not infer from
-- an algebraically consistent witness that original solar input exists.
-- Numeric source magnitudes are deliberately independent physical gates.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound
import DASHI.Physics.Motors.SmithFilsingerReplenishedCycleCapExact as Cycle
import DASHI.Physics.Motors.SmithFilsingerSourceMaxwellBoundaryWeldExact as Source
import DASHI.Physics.Motors.SmithFilsingerMidpointPhaseWorkExact as Port

record ConditionalHundredfold : Set where
  field
    restored : Cycle.RepeatableSourceCycle
    excessUsefulWork : Nat
    hundredfoldDelivered :
      Cycle.RepeatableSourceCycle.usefulLoadWork restored
      ≡ (100 * Cycle.RepeatableSourceCycle.controllerWork restored)
          + excessUsefulWork

-- The full 100-fold output and ALL losses must be funded by the
-- independent natural source plus the controller. Stored energy
-- drawdown is unavailable because the imported cycle is restored.
hundredfoldRequiresSourcedWork :
  (r : ConditionalHundredfold) →
  let c = ConditionalHundredfold.restored r in
    Cycle.RepeatableSourceCycle.naturalSourceWork c
      + Cycle.RepeatableSourceCycle.controllerWork c
    ≡ ((100 * Cycle.RepeatableSourceCycle.controllerWork c)
          + ConditionalHundredfold.excessUsefulWork r)
      + Cycle.RepeatableSourceCycle.allHeatAndOutgoing c
hundredfoldRequiresSourcedWork r =
  trans
    (Cycle.workPaidAfterStorageReturns (ConditionalHundredfold.restored r))
    (cong
      (λ work → work + Cycle.RepeatableSourceCycle.allHeatAndOutgoing
        (ConditionalHundredfold.restored r))
      (ConditionalHundredfold.hundredfoldDelivered r))

-- Stronger: the natural-plus-controller budget must actually dominate
-- 100 x the controller. It cannot be supplied by phase readout or Green
-- amplitude alone. Reuses the ORIGINAL Nat order relation and bound.
hundredfoldNeedsBudget :
  (r : ConditionalHundredfold) →
  let c = ConditionalHundredfold.restored r in
  Bound._≤_
    (100 * Cycle.RepeatableSourceCycle.controllerWork c)
    (Cycle.RepeatableSourceCycle.naturalSourceWork c
      + Cycle.RepeatableSourceCycle.controllerWork c)
hundredfoldNeedsBudget r =
  Cycle.≤-trans
    (Bound.transportUpper
      (Bound.sym (ConditionalHundredfold.hundredfoldDelivered r))
      (Bound.≤-append
        (100 * Cycle.RepeatableSourceCycle.controllerWork
          (ConditionalHundredfold.restored r))
        (ConditionalHundredfold.excessUsefulWork r)))
    (Cycle.loadBoundByReplenishmentAndController
      (ConditionalHundredfold.restored r))

-- Mathematical witness. 100 natural + 1 controller pays 100 useful and
-- 1 heat, all stores restored to 5. Not a measured original solar source.
hypotheticalHundredfoldCycle : Cycle.RepeatableSourceCycle
hypotheticalHundredfoldCycle =
  Cycle.repeatableSourceCycle 100 1 5 5 100 1 refl refl

hypotheticalHundredfold : ConditionalHundredfold
hypotheticalHundredfold = record
  { restored = hypotheticalHundredfoldCycle
  ; excessUsefulWork = zero
  ; hundredfoldDelivered = refl
  }

hypotheticalHundredfoldFunding :
  Cycle.RepeatableSourceCycle.naturalSourceWork hypotheticalHundredfoldCycle
    + Cycle.RepeatableSourceCycle.controllerWork hypotheticalHundredfoldCycle
  ≡ ((100 * Cycle.RepeatableSourceCycle.controllerWork hypotheticalHundredfoldCycle)
        + zero)
    + Cycle.RepeatableSourceCycle.allHeatAndOutgoing hypotheticalHundredfoldCycle
hypotheticalHundredfoldFunding =
  hundredfoldRequiresSourcedWork hypotheticalHundredfold

-- Same-original source certification remains a separate real evidence
-- obligation in Source.SignedSourceCycleWeld: independently calibrated
-- current/voltage, natural incident-minus-outgoing and storage return.
-- This example is never an inhabitant of that original physical record.
