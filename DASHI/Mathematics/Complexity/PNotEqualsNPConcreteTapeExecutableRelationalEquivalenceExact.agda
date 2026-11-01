module DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeExecutableRelationalEquivalenceExact where

------------------------------------------------------------------------
-- EXECUTABLE ROW SEMANTICS = RELATIONAL WELL-FORMED SEMANTICS
--
-- The proof-producing executor in IntrinsicOperationalStep returns a package,
-- which makes a literal `Maybe TapeRow` converse awkward because proof fields
-- participate in package equality.  This owner projects the SAME sequential
-- first-match computation to its observable output row and proves that, under
-- the existing dispatch-uniqueness premise, this projected executable
-- semantics is extensionally equivalent to WellFormedMachineStep.
--
-- No new machine semantics is introduced: the definition below is exactly
-- `executeInteriorRow` with the proof package erased.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Data.Product using (Σ; _×_; _,_)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeLocalityCharacterizationExact as Character
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRuleTableInterpreterExact as Interpreter
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeExecutableWindowStepExact as Window
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRuleKeyDeterminismExact as Determinism
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRelationalRuleAgreementExact as Agreement
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRelationalAfterRowExact as After

------------------------------------------------------------------------
-- Proof-erased observable executor on the exact intrinsic row decomposition.
------------------------------------------------------------------------

executeInteriorAfter :
  ∀ {machine row} →
  Character.InteriorHeadConfiguration machine row →
  Maybe (Local.TapeRow machine)
executeInteriorAfter {machine} interior
    with Character.rowShape interior
... | refl
    with Interpreter.fetchConcreteRule
      machine
      (Character.headState interior)
      (Character.readSymbol interior)
...   | nothing = nothing
...   | just matched =
  just
    (Window.afterRowForRule
      machine
      (Character.prefix interior)
      (Character.leftSymbol interior)
      (Character.rightSymbol interior)
      (Character.suffix interior)
      (Interpreter.rule matched))

------------------------------------------------------------------------
-- Successful executable output is a genuine WellFormedMachineStep.
------------------------------------------------------------------------

executeInteriorAfterSound :
  ∀ {machine before after}
    (interior : Character.InteriorHeadConfiguration machine before) →
  executeInteriorAfter interior ≡ just after →
  WF.WellFormedMachineStep machine before after
executeInteriorAfterSound {machine} interior execution
    with Character.rowShape interior
... | refl
    with Interpreter.fetchConcreteRule
      machine
      (Character.headState interior)
      (Character.readSymbol interior)
...   | nothing = ()
...   | just matched
    with execution
...     | refl = record
  { WF.step =
      Window.listedMatchingRuleIsMachineStep
        machine
        (Character.prefix interior)
        (Character.leftSymbol interior)
        (Character.headState interior)
        (Character.readSymbol interior)
        (Character.rightSymbol interior)
        (Character.suffix interior)
        (Interpreter.rule matched)
        (Interpreter.occurs matched)
        (Interpreter.sourceExact matched)
        (Interpreter.readExact matched)
  ; WF.wellFormedOccurrence = record
      { WF.occurrence =
          Local.occurrence
            (Window.listedMatchingRuleIsMachineStep
              machine
              (Character.prefix interior)
              (Character.leftSymbol interior)
              (Character.headState interior)
              (Character.readSymbol interior)
              (Character.rightSymbol interior)
              (Character.suffix interior)
              (Interpreter.rule matched)
              (Interpreter.occurs matched)
              (Interpreter.sourceExact matched)
              (Interpreter.readExact matched))
      ; WF.prefixPlain = Character.prefixPlain interior
      ; WF.suffixPlain = Character.suffixPlain interior
      }
  }

------------------------------------------------------------------------
-- Every relational well-formed step is reproduced by the executable lookup.
--
-- We use the intrinsic before-row decomposition extracted from the relational
-- step itself.  RuleDispatchUnique identifies first-match with the relational
-- rule, and the existing after-row owner identifies the canonical executable
-- row with the relational output row.
------------------------------------------------------------------------

wellFormedStepIsExecutable :
  ∀ {machine before after}
    (deterministic : Determinism.RuleKeyDeterministic machine)
    (wellFormed : WF.WellFormedMachineStep machine before after) →
  executeInteriorAfter
      (Character.wellFormedStepBeforeInterior wellFormed)
    ≡ just after
wellFormedStepIsExecutable {machine} deterministic wellFormed
    with Agreement.firstMatchAgreesWithWellFormedStepRule
      deterministic wellFormed
... | matched , fetchEq , ruleEq
    with Local.ruleIsConfigured (WF.step wellFormed)
...   | Local.realizes-left =
  helper matched fetchEq ruleEq
...   | Local.realizes-stay =
  helper matched fetchEq ruleEq
...   | Local.realizes-right =
  helper matched fetchEq ruleEq
  where
    interior = Character.wellFormedStepBeforeInterior wellFormed

    helper :
      (matched : Interpreter.MatchedRule
        machine
        (Character.headState interior)
        (Character.readSymbol interior)
        (Local.rules machine)) →
      Interpreter.fetchConcreteRule
        machine
        (Character.headState interior)
        (Character.readSymbol interior)
        ≡ just matched →
      Interpreter.rule matched ≡ Local.rule (WF.step wellFormed) →
      executeInteriorAfter interior ≡ just after
    helper matched fetchEq refl
      rewrite Character.rowShape interior
            | fetchEq
            | After.relationalAfterRowEqualsExecutableAfterRow wellFormed =
      refl

------------------------------------------------------------------------
-- Extensional equivalence on the intrinsic row selected by a relational step.
------------------------------------------------------------------------

executeInteriorAfterIffWellFormed :
  ∀ {machine before after}
    (deterministic : Determinism.RuleKeyDeterministic machine)
    (wellFormed : WF.WellFormedMachineStep machine before after) →
  executeInteriorAfter
      (Character.wellFormedStepBeforeInterior wellFormed)
      ≡ just after
    × WF.WellFormedMachineStep machine before after
executeInteriorAfterIffWellFormed deterministic wellFormed =
  wellFormedStepIsExecutable deterministic wellFormed , wellFormed

------------------------------------------------------------------------
-- MAX-CUT STATUS
--
-- PAID:
-- * the projected executable uses the exact existing first-match interpreter;
-- * successful execution produces a literal WellFormedMachineStep;
-- * every relational WellFormedMachineStep is reproduced by execution under
--   the repository's existing RuleDispatchUnique premise;
-- * the returned executable row is exactly the relational output row.
--
-- LOCAL SEMANTICS FREEZE:
-- No further row/window/rule-table machinery is required for the complexity
-- substrate.  Downstream work should consume this owner and leave the local
-- machine semantics closed.
--
-- NEXT STANDARD BRIDGE:
-- * standard deterministic TM <-> ConcreteTapeMachine polynomial simulation;
-- * language preservation and polynomial clock transport in both directions;
-- * then freeze all representation infrastructure and return to the universal
--   SAT lower-bound theorem.
------------------------------------------------------------------------
