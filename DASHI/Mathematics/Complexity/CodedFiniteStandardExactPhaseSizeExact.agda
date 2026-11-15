module DASHI.Mathematics.Complexity.CodedFiniteStandardExactPhaseSizeExact where

------------------------------------------------------------------------
-- EXACT SIZE ACCOUNTING FOR THE FINITE-CONTROL PHASE LIFT
--
-- The exact-T phase lift pays quiescent handoff by expanding finite control.
-- This module quantifies that payment exactly:
--
--   states = |Q| * (T + 1)
--   rules  = T * |R|.
--
-- This matters for the self-Cook diagonal because the phase-lifted program text
-- itself becomes part of the described machine.  Endpoint quiescence is paid,
-- but program-size feedback is not free.  A compact runtime counter therefore
-- remains a legitimate alternative architecture to compare against the phase
-- lift when closing the final same-object resource fixed point.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedFiniteStandardModeSumExact as Mode
import DASHI.Mathematics.Complexity.CodedFiniteStandardExactPhaseLiftExact as Phase

------------------------------------------------------------------------
-- 1. Tiny list-length algebra on the exact compilation functions.
------------------------------------------------------------------------

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ rest) = suc (listLength rest)

mapFinSucLength :
  ∀ {n : Nat}
    (xs : List (Fin.Fin n)) →
  listLength (Coded.mapFinSuc xs) ≡ listLength xs
mapFinSucLength [] = refl
mapFinSucLength (x ∷ xs)
  rewrite mapFinSucLength xs = refl

allFinLengthExact :
  (n : Nat) →
  listLength (Coded.allFin n) ≡ n
allFinLengthExact zero = refl
allFinLengthExact (suc n)
  rewrite mapFinSucLength (Coded.allFin n)
        | allFinLengthExact n =
  refl

appendLength :
  ∀ {A : Set}
    (left right : List A) →
  listLength (Mode.append left right)
  ≡ listLength left + listLength right
appendLength [] right = refl
appendLength (x ∷ left) right
  rewrite appendLength left right = refl

mapPhaseRulesLength :
  ∀ {states symbols steps : Nat}
    (phase : Fin.Fin steps)
    (rules : List
      (Local.TapeRule
        (Fin.Fin states)
        (Fin.Fin symbols))) →
  listLength (Phase.mapPhaseRules phase rules)
  ≡ listLength rules
mapPhaseRulesLength phase [] = refl
mapPhaseRulesLength phase (rule ∷ rest)
  rewrite mapPhaseRulesLength phase rest = refl

compilePhasesLength :
  ∀ {states symbols steps : Nat}
    (phases : List (Fin.Fin steps))
    (rules : List
      (Local.TapeRule
        (Fin.Fin states)
        (Fin.Fin symbols))) →
  listLength (Phase.compilePhases phases rules)
  ≡ listLength phases * listLength rules
compilePhasesLength [] rules = refl
compilePhasesLength (phase ∷ phases) rules
  rewrite appendLength
            (Phase.mapPhaseRules phase rules)
            (Phase.compilePhases phases rules)
        | mapPhaseRulesLength phase rules
        | compilePhasesLength phases rules =
  refl

------------------------------------------------------------------------
-- 2. Exact phase-lift size theorems.
------------------------------------------------------------------------

phaseLiftStateCountExact :
  (source : Coded.CodedFiniteStandardTM) →
  (steps : Nat) →
  Coded.stateCount (Phase.phaseLiftCode source steps)
  ≡ Coded.stateCount source * suc steps
phaseLiftStateCountExact source steps = refl

phaseLiftRuleCountExact :
  (source : Coded.CodedFiniteStandardTM) →
  (steps : Nat) →
  listLength (Coded.rules (Phase.phaseLiftCode source steps))
  ≡ steps * listLength (Coded.rules source)
phaseLiftRuleCountExact source steps
  rewrite compilePhasesLength
            (Coded.allFin steps)
            (Coded.rules source)
        | allFinLengthExact steps =
  refl

------------------------------------------------------------------------
-- 3. Max-cut / attribution boundary.
------------------------------------------------------------------------

record PhaseLiftSizeBoundary : Set where
  constructor phase-lift-size-boundary
  field
    exactQuiescentBoundaryPaid : Bool
    stateBlowupLinearInExactBudget : Bool
    ruleBlowupLinearInExactBudget : Bool
    programTextOverheadIsZero : Bool
    compactRuntimeCounterStillWorthComparing : Bool
    xorGridOrIITImpliesComplexityHardness : Bool

open PhaseLiftSizeBoundary public

canonicalPhaseLiftSizeBoundary : PhaseLiftSizeBoundary
canonicalPhaseLiftSizeBoundary =
  phase-lift-size-boundary
    true true true false true false

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- The phase lift is a correct exact-T quiescence compiler, but its finite code
-- expands linearly with T.  For the final self-Cook construction this expansion
-- must be included in the described target and therefore in the fixed-point
-- resource audit.  The XOR/ripple-counter route is not required for endpoint
-- correctness, but it remains a productive competing implementation because it
-- can trade runtime counter work for a smaller static program description.
------------------------------------------------------------------------
