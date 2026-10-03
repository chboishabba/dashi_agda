module DASHI.Mathematics.Complexity.ConcreteTapeStandardOneStepExact where

------------------------------------------------------------------------
-- CONCRETE ROW -> CONVENTIONAL SPLIT-TAPE ONE-STEP WELD
--
-- This owner projects the already-proved intrinsic concrete row decomposition
-- onto the conventional split-tape configuration of StandardSingleTapeMachine.
-- The left list is nearest-cell-first.  We therefore reverse the proven-plain
-- row-order prefix structurally with `farLeftSymbols`: the immediate left cell
-- remains visibly at the head of the standard left tape, while farther-left
-- cells are appended in reverse row order.
--
-- For each of the three literal rule directions, the conventional standard
-- step is exactly the projection of the concrete radius-one rewrite.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (nothing; just)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeLocalityCharacterizationExact as Character
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRuleTableInterpreterExact as Interpreter
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRuleKeyDeterminismExact as Determinism
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRelationalRuleAgreementExact as Agreement
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard

------------------------------------------------------------------------
-- Erase proof-known-plain cell lists to symbol lists.
------------------------------------------------------------------------

plainSymbols :
  ∀ {State Symbol : Set}
    {cells : List (Local.TapeCell State Symbol)} →
  WF.PlainCells cells → List Symbol
plainSymbols WF.plainNil = []
plainSymbols (WF.plainCons {symbol = symbol} rest) =
  symbol ∷ plainSymbols rest

/-- Symbols lying strictly farther left than the immediate left neighbour,
written nearest-head-first for the conventional split-tape model. -/
farLeftSymbols :
  ∀ {State Symbol : Set}
    {cells : List (Local.TapeCell State Symbol)} →
  WF.PlainCells cells → List Symbol
farLeftSymbols WF.plainNil = []
farLeftSymbols (WF.plainCons {symbol = symbol} rest) =
  Local.append (farLeftSymbols rest) (symbol ∷ [])

------------------------------------------------------------------------
-- Intrinsic before-row projection.
------------------------------------------------------------------------

standardBeforeOfInterior :
  ∀ {machine row} →
  Character.InteriorHeadConfiguration machine row →
  Standard.StandardConfiguration (Standard.standardControlOfConcrete machine)
standardBeforeOfInterior interior =
  Standard.standard-configuration
    (Character.leftSymbol interior ∷
      farLeftSymbols (Character.prefixPlain interior))
    (Character.headState interior)
    (Character.readSymbol interior)
    (Character.rightSymbol interior ∷
      plainSymbols (Character.suffixPlain interior))

------------------------------------------------------------------------
-- Projection of the concrete after-row determined by a selected rule.
------------------------------------------------------------------------

standardAfterOfRule :
  ∀ {machine row} →
  (interior : Character.InteriorHeadConfiguration machine row) →
  Local.TapeRule (Local.State machine) (Local.Symbol machine) →
  Standard.StandardConfiguration (Standard.standardControlOfConcrete machine)
standardAfterOfRule interior rule
    with Local.direction rule
... | Local.moveLeft =
  Standard.standard-configuration
    (farLeftSymbols (Character.prefixPlain interior))
    (Local.targetState rule)
    (Character.leftSymbol interior)
    (Local.writeSymbol rule ∷
      Character.rightSymbol interior ∷
      plainSymbols (Character.suffixPlain interior))
... | Local.stayPut =
  Standard.standard-configuration
    (Character.leftSymbol interior ∷
      farLeftSymbols (Character.prefixPlain interior))
    (Local.targetState rule)
    (Local.writeSymbol rule)
    (Character.rightSymbol interior ∷
      plainSymbols (Character.suffixPlain interior))
... | Local.moveRight =
  Standard.standard-configuration
    (Local.writeSymbol rule ∷
      Character.leftSymbol interior ∷
      farLeftSymbols (Character.prefixPlain interior))
    (Local.targetState rule)
    (Character.rightSymbol interior)
    (plainSymbols (Character.suffixPlain interior))

------------------------------------------------------------------------
-- Directional standard execution is exactly the projected concrete rewrite.
------------------------------------------------------------------------

standardApplyMatchedRuleExact :
  ∀ {machine row q a rules}
    (interior : Character.InteriorHeadConfiguration machine row)
    (matched : Interpreter.MatchedRule machine q a rules) →
  Standard.standardApplyTransition
    (Standard.standardControlOfConcrete machine)
    (standardBeforeOfInterior interior)
    (Standard.matchedRuleTransition matched)
  ≡ standardAfterOfRule interior (Interpreter.rule matched)
standardApplyMatchedRuleExact interior matched
    with Interpreter.rule matched
... | Local.tape-rule source read target write Local.moveLeft = refl
... | Local.tape-rule source read target write Local.stayPut = refl
... | Local.tape-rule source read target write Local.moveRight = refl

------------------------------------------------------------------------
-- The actual first-match interpreter therefore produces exactly one standard
-- split-tape step on the projected row.
------------------------------------------------------------------------

standardNext_of_fetch :
  ∀ {machine row matched}
    (interior : Character.InteriorHeadConfiguration machine row) →
  Interpreter.fetchConcreteRule
      machine
      (Character.headState interior)
      (Character.readSymbol interior)
    ≡ just matched →
  Standard.standardNext
      (Standard.standardControlOfConcrete machine)
      (standardBeforeOfInterior interior)
    ≡ just (standardAfterOfRule interior (Interpreter.rule matched))
standardNext_of_fetch {machine} interior fetchEq
    rewrite fetchEq =
  congrJust (standardApplyMatchedRuleExact interior _)
  where
    congrJust : ∀ {A : Set} {x y : A} → x ≡ y → just x ≡ just y
    congrJust refl = refl

standardNext_nothing :
  ∀ {machine row}
    (interior : Character.InteriorHeadConfiguration machine row) →
  Interpreter.fetchConcreteRule
      machine
      (Character.headState interior)
      (Character.readSymbol interior)
    ≡ nothing →
  Standard.standardNext
      (Standard.standardControlOfConcrete machine)
      (standardBeforeOfInterior interior)
    ≡ nothing
standardNext_nothing {machine} interior fetchEq
    rewrite fetchEq = refl

------------------------------------------------------------------------
-- Relational concrete steps agree with the same standard step under the
-- existing deterministic-key premise.
------------------------------------------------------------------------

wellFormedConcreteStepProjectsToStandardStep :
  ∀ {machine before after}
    (deterministic : Determinism.RuleKeyDeterministic machine)
    (wellFormed : WF.WellFormedMachineStep machine before after) →
  let interior = Character.wellFormedStepBeforeInterior wellFormed in
  Standard.standardNext
      (Standard.standardControlOfConcrete machine)
      (standardBeforeOfInterior interior)
    ≡ just (standardAfterOfRule interior (Local.rule (WF.step wellFormed)))
wellFormedConcreteStepProjectsToStandardStep
    deterministic wellFormed
    with Agreement.firstMatchAgreesWithWellFormedStepRule
      deterministic wellFormed
... | matched , fetchEq , ruleEq
    rewrite ruleEq =
  standardNext_of_fetch
    (Character.wellFormedStepBeforeInterior wellFormed)
    fetchEq

------------------------------------------------------------------------
-- MAX-CUT STATUS
--
-- PAID (subject to exact-head Agda certification):
-- * proof-preserving extraction of symbol lists from concrete plain contexts;
-- * structural nearest-head-first reversal of the concrete left prefix;
-- * actual intrinsic concrete before row -> conventional split-tape config;
-- * exact left/stay/right correspondence for the same selected rule;
-- * first-match concrete execution -> standard execution;
-- * relational WellFormedMachineStep -> the same standard execution under
--   RuleDispatchUnique.
--
-- NEXT:
-- * identify these intrinsic before/after projections with the canonical
--   ExactlyOneHead projection;
-- * iterate through WellFormedTapeRun;
-- * prove polynomial clock/language transport and freeze P infrastructure.
------------------------------------------------------------------------
