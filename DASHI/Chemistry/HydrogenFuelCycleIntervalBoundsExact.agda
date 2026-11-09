module DASHI.Chemistry.HydrogenFuelCycleIntervalBoundsExact where

-- Attribution: constructive natural-number order is standard Agda/DASHI
-- mathematical prior art. This interval admission and its use for the user's
-- hydrogen/fuel audit were drafted with ChatGPT (2026-11-09).
-- No experimental uncertainty bound is inferred from patent/vendor statements.

open import Agda.Builtin.Nat using (Nat; _+_; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_; _<_)
open import Data.Nat.Properties as NatP using (+-mono-≤)
open import Relation.Binary.PropositionalEquality using (sym; subst)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using ()
open import Relation.Binary.PropositionalEquality using (trans)

record Interval : Set where
  constructor interval
  field
    lower : Nat
    upper : Nat
    ordered : lower ≤ upper

open Interval public

record Inside (x : Nat) (i : Interval) : Set where
  field
    aboveLower : lower i ≤ x
    belowUpper : x ≤ upper i

open Inside public

-- An exact sum interval. Keeping the two interval carriers, their
-- nonnegative endpoints, and their order prevents nominal-value arithmetic
-- from silently replacing independent instrument error envelopes.
addInterval : Interval → Interval → Interval
addInterval a b = interval
  (lower a + lower b)
  (upper a + upper b)
  (+-mono-≤ (ordered a) (ordered b))

-- For two independent energy streams, true total input belongs to the
-- sum interval if each input belongs to its respective interval.
insideSum :
  (a b : Interval) (x y : Nat) →
  Inside x a → Inside y b →
  Inside (x + y) (addInterval a b)
insideSum a b x y xa yb = record
  { aboveLower = +-mono-≤ (aboveLower xa) (aboveLower yb)
  ; belowUpper = +-mono-≤ (belowUpper xa) (belowUpper yb)
  }

-- A strict comparison of input energy is *guaranteed* across a metered
-- range only when the highest possible assisted input is below the lowest
-- possible baseline input.
record RobustEnergySaving : Set where
  field
    baselineFuel : Interval
    assistedFuel : Interval
    externalElectricity : Interval
    strictSeparation :
      upper (addInterval assistedFuel externalElectricity)
      < lower baselineFuel

open RobustEnergySaving public

robustSavingAtEveryAdmittedReading :
  (r : RobustEnergySaving) →
  (f₀ f₁ b : Nat) →
  Inside f₀ (baselineFuel r) →
  Inside f₁ (assistedFuel r) →
  Inside b (externalElectricity r) →
  f₁ + b < f₀
robustSavingAtEveryAdmittedReading r f₀ f₁ b in₀ in₁ inB =
  NatP.<-≤-trans
    (NatP.≤-<-trans
      (belowUpper
        (insideSum (assistedFuel r) (externalElectricity r)
          f₁ b in₁ inB))
      (strictSeparation r))
    (aboveLower in₀)

-- These are separate, evidence-priced quantities. An experimental result
-- requires exact source-to-instrument links, time-window alignment,
-- uncertainty coverage, and common useful output.
record IntervalRunReceipt : Set₁ where
  field
    comparison : RobustEnergySaving
    actualBaselineDiesel : Nat
    actualAssistedDiesel : Nat
    actualExternalElectricalInput : Nat
    baselineWithin : Inside actualBaselineDiesel (baselineFuel comparison)
    assistedWithin : Inside actualAssistedDiesel (assistedFuel comparison)
    electricalWithin :
      Inside actualExternalElectricalInput (externalElectricity comparison)
    commonOutputAndOperatingEnvelope : Set
    measurementProvenance : Set

actualInputReduction :
  (r : IntervalRunReceipt) →
  IntervalRunReceipt.actualAssistedDiesel r
    + IntervalRunReceipt.actualExternalElectricalInput r
    < IntervalRunReceipt.actualBaselineDiesel r
actualInputReduction r =
  robustSavingAtEveryAdmittedReading
    (IntervalRunReceipt.comparison r)
    (IntervalRunReceipt.actualBaselineDiesel r)
    (IntervalRunReceipt.actualAssistedDiesel r)
    (IntervalRunReceipt.actualExternalElectricalInput r)
    (IntervalRunReceipt.baselineWithin r)
    (IntervalRunReceipt.assistedWithin r)
    (IntervalRunReceipt.electricalWithin r)
