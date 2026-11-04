module DASHI.Mathematics.Complexity.PNotEqualsNPPhaseCounterParetoExact where

------------------------------------------------------------------------
-- PHASE-EXPANDED CONTROL VS COMPACT XOR/RIPPLE COUNTER
--
-- This owner does not choose a winner by slogan.  It places the two already-
-- implemented timing constructions on one explicit resource surface.
--
-- Phase-expanded construction:
--   states = |Q| * (T+1)
--   rules  = T * |R|
-- and the terminal phase is quiescent.
--
-- Compact XOR/ripple construction:
--   timer control states = 3
--   timer rules          = 3
--   one decrement run is literal standard-TM execution
--   one decrement work <= timer bit-width + 1, with the bound attained by an
--   all-zero word.
--
-- The compact counter therefore trades static program growth for runtime tape
-- work.  It does NOT make that runtime free: repeated reset/decrement, travel
-- between candidate and timer regions, and the final same-object Cook budget
-- remain explicit obligations.
--
-- Attribution boundary:
-- The IIT/XOR-grid programme motivated the bipermutative/XOR implementation
-- choice.  Complexity authority here is entirely the locally reproved DASHI
-- countdown semantics/rule-table/run/cost owners.  No IIT phi quantity or
-- causal-irreducibility claim is imported as a lower-bound theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat.Base using (_≤_)

import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedFiniteStandardExactPhaseLiftExact as PhaseLift
import DASHI.Mathematics.Complexity.CodedFiniteStandardExactPhaseSizeExact as Phase
import DASHI.Mathematics.Complexity.PNotEqualsNPBinaryCountdownCostExact as Cost
import DASHI.Mathematics.Complexity.PNotEqualsNPBinaryCountdownExactRunExact as CounterRun

------------------------------------------------------------------------
-- 1. Compact timer has constant finite control / rule-table size.
------------------------------------------------------------------------

compactCounterStateCountExact :
  Coded.stateCount CounterRun.countdownCode
    ≡ suc (suc (suc zero))
compactCounterStateCountExact = refl

compactCounterRuleCountExact :
  Phase.listLength (Coded.rules CounterRun.countdownCode)
    ≡ suc (suc (suc zero))
compactCounterRuleCountExact = refl

------------------------------------------------------------------------
-- 2. Runtime decrement work is width-bounded, not hidden.
------------------------------------------------------------------------

compactCounterSingleDecrementBound :
  (bits : List Bool) →
  Cost.countdownWork bits ≤ suc (Cost.bitWidth bits)
compactCounterSingleDecrementBound = Cost.countdownWorkBound

------------------------------------------------------------------------
-- 3. Re-export the exact static phase-lift accounting on the same surface.
------------------------------------------------------------------------

phaseExpandedStateCountExact :
  (source : Coded.CodedFiniteStandardTM) →
  (steps : Nat) →
  Coded.stateCount (PhaseLift.phaseLiftCode source steps)
    ≡ Coded.stateCount source * suc steps
phaseExpandedStateCountExact = Phase.phaseLiftStateCountExact

phaseExpandedRuleCountExact :
  (source : Coded.CodedFiniteStandardTM) →
  (steps : Nat) →
  Phase.listLength
      (Coded.rules (PhaseLift.phaseLiftCode source steps))
    ≡ steps * Phase.listLength (Coded.rules source)
phaseExpandedRuleCountExact = Phase.phaseLiftRuleCountExact

------------------------------------------------------------------------
-- 4. Pareto boundary: neither coordinate may be hidden by the other.
------------------------------------------------------------------------

record PhaseCounterParetoBoundary : Set where
  constructor phase-counter-pareto-boundary
  field
    phaseExactQuiescentHandoffPaid : Bool
    phaseStaticStateGrowthLinearInT : Bool
    phaseStaticRuleGrowthLinearInT : Bool
    compactCounterConstantControlSizePaid : Bool
    compactCounterConstantRuleCountPaid : Bool
    compactCounterArbitraryWordExactRunPaid : Bool
    compactCounterSingleDecrementWidthBoundPaid : Bool
    compactCounterWorstCaseWidthBoundTight : Bool
    compactCounterResetStillRequired : Bool
    compactCounterCandidateHeadTravelStillRequired : Bool
    finalSameCookBudgetClosureStillRequired : Bool
    oneArchitectureDominatesAllResources : Bool
    iitPhiIsComplexityLowerBound : Bool

open PhaseCounterParetoBoundary public

canonicalPhaseCounterParetoBoundary : PhaseCounterParetoBoundary
canonicalPhaseCounterParetoBoundary =
  phase-counter-pareto-boundary
    true true true
    true true true true true
    true true true
    false false

noFreeTimingArchitecture :
  oneArchitectureDominatesAllResources canonicalPhaseCounterParetoBoundary
    ≡ false
noFreeTimingArchitecture = refl

sameBudgetStillOpen :
  finalSameCookBudgetClosureStillRequired canonicalPhaseCounterParetoBoundary
    ≡ true
sameBudgetStillOpen = refl

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- The exact phase lift and compact ripple timer are now comparable without
-- conflating static program description with runtime work.  The behavioural
-- self-specializer may choose either implementation, but the final self-Cook
-- resource theorem must charge the selected route on BOTH axes.
------------------------------------------------------------------------
