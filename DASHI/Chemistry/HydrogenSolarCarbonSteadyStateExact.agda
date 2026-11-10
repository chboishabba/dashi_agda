module DASHI.Chemistry.HydrogenSolarCarbonSteadyStateExact where

-- Attribution / statement of scope, 2026-11-10:
-- Conventional finite-recycling material accounting and standard Nat
-- polynomial algebra are scientific/mathematical prior art. Reuses
-- DASHI's carbon-path, Atomic369 and source-specific SI ownership.
-- The user defined the hydrocarbon power-station proposal: co-located
-- solar electricity produces H2 from water; flue/DAC carbon is converted
-- to fuel to reduce fresh fossil extraction. This formula is a new
-- user-directed, ChatGPT-authored conditional source integration.
--
-- IMPORTANT: two DIFFERENT regimes.
-- (A) Finite original carbon batch with no external makeup: useful carbon
--     decreases by yield at each cycle, and so does output.
-- (B) Fixed carbon-fuel demand each operating period: any unrecovered
--     carbon must be replaced; the desired steady-output case.
-- This file formalises (B) only, *not* an immortal batch of carbon.

open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

import DASHI.Chemistry.HydrogenSolarCarbonGeneralStoichiometryExact as Chemistry
import DASHI.Physics.Units.SI as SI

record FixedOutputCarbonCycle : Set where
  field
    demandedCarbonAtoms : Nat
    recoveredPercent : Nat
    freshPercent : Nat
    fullSourceSplit : recoveredPercent + freshPercent ≡ 100
open FixedOutputCarbonCycle public

-- Carbon atoms in this natural-number model are represented in
-- percent-weighted units; a 100x scale avoids rounding q*C.
reusedCarbonScaled : FixedOutputCarbonCycle → Nat
reusedCarbonScaled c = recoveredPercent c * demandedCarbonAtoms c

freshCarbonScaled : FixedOutputCarbonCycle → Nat
freshCarbonScaled c = freshPercent c * demandedCarbonAtoms c

requiredCarbonScaled : FixedOutputCarbonCycle → Nat
requiredCarbonScaled c = 100 * demandedCarbonAtoms c

-- A direct rewrite using the independently admitted full source split
-- avoids equating arbitrary r+v with 100 by arithmetic alone.
actualSourceBalance :
  (c : FixedOutputCarbonCycle) →
  reusedCarbonScaled c + freshCarbonScaled c
    ≡ requiredCarbonScaled c
actualSourceBalance c =
  transSource c
  where
    open import Relation.Binary.PropositionalEquality using (cong; trans)
    splitDistributivity :
      (a b n : Nat) → a * n + b * n ≡ (a + b) * n
    splitDistributivity a b n =
      solve 3
        (λ a b n → (a :* n) :+ (b :* n)
          := (a :+ b) :* n)
        refl a b n
    transSource :
      (c : FixedOutputCarbonCycle) →
      reusedCarbonScaled c + freshCarbonScaled c
        ≡ requiredCarbonScaled c
    transSource c =
      trans
        (splitDistributivity (recoveredPercent c)
          (freshPercent c) (demandedCarbonAtoms c))
        (cong (λ p → p * demandedCarbonAtoms c)
          (fullSourceSplit c))

-- For 1 initial full-fossil period plus n subsequent periods, at the
-- same carbon throughput: virgin demand = initial amount + n*makeup.
-- Relative to n+1 virgin-only periods, saved virgin carbon is n*recycled.
virginWithRecirculationScaled :
  Nat → FixedOutputCarbonCycle → Nat
virginWithRecirculationScaled later c =
  requiredCarbonScaled c + later * freshCarbonScaled c

virginWithoutRecirculationScaled :
  Nat → FixedOutputCarbonCycle → Nat
virginWithoutRecirculationScaled later c =
  requiredCarbonScaled c + later * requiredCarbonScaled c

recycledVirginDisplacement :
  (later : Nat) (c : FixedOutputCarbonCycle) →
  virginWithRecirculationScaled later c
    + later * reusedCarbonScaled c
      ≡ virginWithoutRecirculationScaled later c
recycledVirginDisplacement later c =
  rewriteHelper later c
  where
  open import Relation.Binary.PropositionalEquality using (cong; trans)
  rearrange :
    (n d v r : Nat) →
    (d + n * v) + n * r ≡ d + n * (v + r)
  rearrange n d v r =
    solve 4
      (λ n d v r → (d :+ (n :* v)) :+ (n :* r)
        := d :+ (n :* (v :+ r)))
      refl n d v r
  rewriteHelper :
    (later : Nat) (c : FixedOutputCarbonCycle) →
    virginWithRecirculationScaled later c +
      later * reusedCarbonScaled c
      ≡ virginWithoutRecirculationScaled later c
  rewriteHelper later c =
    trans (rearrange later (requiredCarbonScaled c)
      (freshCarbonScaled c) (reusedCarbonScaled c))
      (cong (λ n → requiredCarbonScaled c + later * n)
        (trans
          (solve 2
            (λ a b → a :+ b := b :+ a)
            refl (freshCarbonScaled c) (reusedCarbonScaled c))
          (actualSourceBalance c)))

-- Source admission and life-cycle equivalence are not discharged by a
-- counting equality. Exhaust carbon that is re-burned can reduce demand
-- for newly extracted carbon, without turning fossil carbon into a permanent
-- atmospheric removal.
record ActualCircularPowerStation : Set₁ where
  field
    selectedCycle : FixedOutputCarbonCycle
    solarElectricInput : SI.Measurement SI.Energy SI.unitScale
    annualMatchedFuelDuty : Set
    actualCarbonCaptureAndMethanationYield : Set
    additionalHydrogenFromWater : Set
    actualFreshHydrocarbonSubstitution : Set
    carbonStorageAndLeakageAndPurge : Set
    lifecycleAtmosphericCO2Baseline : Set
    generatorEfficiencyAndStorage : Set
    heatElectricityDispatchAndWaterAvailability : Set
    independentCalibrationAndReview : Set

-- Hypothetical illustrative source split 90% recovered, 10% makeup.
-- These are example integers, not physical capture/combustion data.
toyCycle : FixedOutputCarbonCycle
toyCycle = record
  { demandedCarbonAtoms = 100
  ; recoveredPercent = 90
  ; freshPercent = 10
  ; fullSourceSplit = refl
  }

toySteadyMakeup :
  freshCarbonScaled toyCycle ≡ 1000
toySteadyMakeup = refl

toySteadyRecovery :
  reusedCarbonScaled toyCycle ≡ 9000
toySteadyRecovery = refl
