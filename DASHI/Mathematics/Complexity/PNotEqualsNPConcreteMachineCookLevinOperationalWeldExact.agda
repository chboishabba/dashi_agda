module DASHI.Mathematics.Complexity.PNotEqualsNPConcreteMachineCookLevinOperationalWeldExact where

------------------------------------------------------------------------
-- SAME-OBJECT OPERATIONAL / COOK--LEVIN WELD
--
-- The repository previously had:
--   * a genuine finite ConcreteTapeMachine and exact Cook--Levin encoding;
--   * a separate operational calibration interpreter.
--
-- PNotEqualsNPConcreteTapeRuleTableInterpreterExact now interprets the
-- ACTUAL ConcreteTapeMachine.rules sequentially. This owner proves that
-- the operational fetch bound and prize-facing Cook--Levin certificate
-- apply to the SAME literal machine object.
--
-- This closes a model-drift gap. It does NOT prove that every standard
-- polynomial-time TM has already been translated into ConcreteTapeMachine,
-- nor any lower bound for SAT.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_; _,_)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinPrizeFacingExact as Prize
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRuleTableInterpreterExact as Interpreter

------------------------------------------------------------------------
-- The operational rule-fetch budget is literally the same rule width that
-- appears in the Cook--Levin selector encoding.
------------------------------------------------------------------------

operationalFetchBoundUsesCookLevinRuleWidth :
  (machine : Local.ConcreteTapeMachine) →
  (q : Local.State machine) →
  (a : Local.Symbol machine) →
  Interpreter.fetchConcreteRuleWork machine q a
  ≤ Selector.RuleWidth machine
operationalFetchBoundUsesCookLevinRuleWidth machine q a =
  Interpreter.fetchConcreteRuleWorkBound machine q a

------------------------------------------------------------------------
-- One theorem returns both facts for the SAME machine:
--   (1) bounded operational transition-table lookup;
--   (2) exact-budget Cook--Levin semantics + exact variable/clause accounting.
------------------------------------------------------------------------

sameMachineOperationalAndCookLevin :
  (machine : Local.ConcreteTapeMachine) →
  (stateCoverage :
    Canonical.EnumerationCoverage (Local.finiteState machine)) →
  (symbolCoverage :
    Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  (nonempty : Selector.NonemptyRuleTable machine) →
  (input : Input.InputWord machine) →
  (steps : Nat) →
  (q : Local.State machine) →
  (a : Local.Symbol machine) →
  (Interpreter.fetchConcreteRuleWork machine q a
    ≤ Selector.RuleWidth machine)
  ×
  Prize.PrizeFacingCookLevinCertificate
    stateCoverage symbolCoverage nonempty input steps
sameMachineOperationalAndCookLevin
    machine stateCoverage symbolCoverage nonempty
    input steps q a =
  operationalFetchBoundUsesCookLevinRuleWidth machine q a
  ,
  Prize.prizeFacingCookLevinCertificate
    stateCoverage symbolCoverage nonempty input steps

------------------------------------------------------------------------
-- MAX-CUT STATUS
--
-- PAID:
--   one finite machine object;
--   operational rule-table fetch on its literal rules;
--   exact finite fetch-cost bound;
--   exact Cook--Levin SAT encoding on the same rule table;
--   exact variable and closed clause accounting from the existing certificate.
--
-- OPEN:
--   standard deterministic TM -> ConcreteTapeMachine simulation;
--   ConcreteTapeMachine -> a standard model simulation;
--   polynomial relation of those two clocks;
--   algorithm-independent SAT lower-bound invariant.
------------------------------------------------------------------------
