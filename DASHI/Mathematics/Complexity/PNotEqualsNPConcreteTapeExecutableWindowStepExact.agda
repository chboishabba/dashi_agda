module DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeExecutableWindowStepExact where

------------------------------------------------------------------------
-- EXECUTABLE WHOLE-ROW STEP FOR THE ACTUAL ConcreteTapeMachine
--
-- The existing rule-table interpreter selects an actual listed rule and
-- proves that its source/read fields match the current head state/symbol.
-- ConcreteTapeMachineLocalityExact separately defines the prize-facing
-- MachineStep relation as a contiguous radius-one row rewrite.
--
-- This owner welds those two objects:
--
--   finite sequential rule lookup
--       -> literal updated TapeRow
--       -> theorem that the produced row is an actual MachineStep.
--
-- It does not introduce a second machine carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRuleTableInterpreterExact as Interpreter

------------------------------------------------------------------------
-- Canonical row with one selected head and an explicit radius-one window.
------------------------------------------------------------------------

beforeRow :
  (machine : Local.ConcreteTapeMachine) →
  List (Local.TapeCell (Local.State machine) (Local.Symbol machine)) →
  Local.Symbol machine →
  Local.State machine →
  Local.Symbol machine →
  Local.Symbol machine →
  List (Local.TapeCell (Local.State machine) (Local.Symbol machine)) →
  Local.TapeRow machine
beforeRow machine prefix left q scanned right suffix =
  Local.tape-row
    (Local.append prefix
      (Local.plain left ∷
       Local.headed q scanned ∷
       Local.plain right ∷
       suffix))

afterRowForRule :
  (machine : Local.ConcreteTapeMachine) →
  List (Local.TapeCell (Local.State machine) (Local.Symbol machine)) →
  Local.Symbol machine →
  Local.Symbol machine →
  List (Local.TapeCell (Local.State machine) (Local.Symbol machine)) →
  Local.TapeRule (Local.State machine) (Local.Symbol machine) →
  Local.TapeRow machine
afterRowForRule machine prefix left right suffix
    (Local.tape-rule q a q' written Local.moveLeft) =
  Local.tape-row
    (Local.append prefix
      (Local.headed q' left ∷
       Local.plain written ∷
       Local.plain right ∷
       suffix))
afterRowForRule machine prefix left right suffix
    (Local.tape-rule q a q' written Local.stayPut) =
  Local.tape-row
    (Local.append prefix
      (Local.plain left ∷
       Local.headed q' written ∷
       Local.plain right ∷
       suffix))
afterRowForRule machine prefix left right suffix
    (Local.tape-rule q a q' written Local.moveRight) =
  Local.tape-row
    (Local.append prefix
      (Local.plain left ∷
       Local.plain written ∷
       Local.headed q' right ∷
       suffix))

------------------------------------------------------------------------
-- Any actually-listed matching rule realizes the corresponding concrete
-- row rewrite.
------------------------------------------------------------------------

listedMatchingRuleIsMachineStep :
  (machine : Local.ConcreteTapeMachine) →
  (prefix :
    List (Local.TapeCell (Local.State machine) (Local.Symbol machine))) →
  (left : Local.Symbol machine) →
  (q : Local.State machine) →
  (scanned right : Local.Symbol machine) →
  (suffix :
    List (Local.TapeCell (Local.State machine) (Local.Symbol machine))) →
  (rule : Local.TapeRule (Local.State machine) (Local.Symbol machine)) →
  Local.RuleOccurs rule (Local.rules machine) →
  Local.sourceState rule ≡ q →
  Local.readSymbol rule ≡ scanned →
  Local.MachineStep
    machine
    (beforeRow machine prefix left q scanned right suffix)
    (afterRowForRule machine prefix left right suffix rule)
listedMatchingRuleIsMachineStep
    machine prefix left q scanned right suffix
    (Local.tape-rule source read target written Local.moveLeft)
    occurs sourceEq readEq
    with sourceEq | readEq
... | refl | refl =
  record
    { Local.rule =
        Local.tape-rule q scanned target written Local.moveLeft
    ; Local.ruleOccursInMachine = occurs
    ; Local.window =
        Local.six-cell-window
          (Local.plain left)
          (Local.headed q scanned)
          (Local.plain right)
          (Local.headed target left)
          (Local.plain written)
          (Local.plain right)
    ; Local.ruleIsConfigured = Local.realizes-left
    ; Local.occurrence = record
        { Local.prefix = prefix
        ; Local.suffix = suffix
        ; Local.beforeShape = refl
        ; Local.afterShape = refl
        }
    }
listedMatchingRuleIsMachineStep
    machine prefix left q scanned right suffix
    (Local.tape-rule source read target written Local.stayPut)
    occurs sourceEq readEq
    with sourceEq | readEq
... | refl | refl =
  record
    { Local.rule =
        Local.tape-rule q scanned target written Local.stayPut
    ; Local.ruleOccursInMachine = occurs
    ; Local.window =
        Local.six-cell-window
          (Local.plain left)
          (Local.headed q scanned)
          (Local.plain right)
          (Local.plain left)
          (Local.headed target written)
          (Local.plain right)
    ; Local.ruleIsConfigured = Local.realizes-stay
    ; Local.occurrence = record
        { Local.prefix = prefix
        ; Local.suffix = suffix
        ; Local.beforeShape = refl
        ; Local.afterShape = refl
        }
    }
listedMatchingRuleIsMachineStep
    machine prefix left q scanned right suffix
    (Local.tape-rule source read target written Local.moveRight)
    occurs sourceEq readEq
    with sourceEq | readEq
... | refl | refl =
  record
    { Local.rule =
        Local.tape-rule q scanned target written Local.moveRight
    ; Local.ruleOccursInMachine = occurs
    ; Local.window =
        Local.six-cell-window
          (Local.plain left)
          (Local.headed q scanned)
          (Local.plain right)
          (Local.plain left)
          (Local.plain written)
          (Local.headed target right)
    ; Local.ruleIsConfigured = Local.realizes-right
    ; Local.occurrence = record
        { Local.prefix = prefix
        ; Local.suffix = suffix
        ; Local.beforeShape = refl
        ; Local.afterShape = refl
        }
    }

------------------------------------------------------------------------
-- Executable selected step.  A successful result carries the produced row
-- and its actual MachineStep witness.
------------------------------------------------------------------------

record ExecutedWindowStep
    (machine : Local.ConcreteTapeMachine)
    (before : Local.TapeRow machine) : Set₁ where
  constructor executed-window-step
  field
    after : Local.TapeRow machine
    witness : Local.MachineStep machine before after

open ExecutedWindowStep public

executeSelectedWindow :
  (machine : Local.ConcreteTapeMachine) →
  (prefix :
    List (Local.TapeCell (Local.State machine) (Local.Symbol machine))) →
  (left : Local.Symbol machine) →
  (q : Local.State machine) →
  (scanned right : Local.Symbol machine) →
  (suffix :
    List (Local.TapeCell (Local.State machine) (Local.Symbol machine))) →
  Maybe
    (ExecutedWindowStep
      machine
      (beforeRow machine prefix left q scanned right suffix))
executeSelectedWindow machine prefix left q scanned right suffix
    with Interpreter.fetchConcreteRule machine q scanned
... | nothing = nothing
... | just matched =
  just
    (executed-window-step
      (afterRowForRule
        machine prefix left right suffix
        (Interpreter.rule matched))
      (listedMatchingRuleIsMachineStep
        machine prefix left q scanned right suffix
        (Interpreter.rule matched)
        (Interpreter.occurs matched)
        (Interpreter.sourceExact matched)
        (Interpreter.readExact matched)))

------------------------------------------------------------------------
-- The sequential fetch cost used by this executable step is bounded by the
-- exact same rule width used by the Cook--Levin selector.
------------------------------------------------------------------------

executeSelectedWindowFetchBound :
  (machine : Local.ConcreteTapeMachine) →
  (q : Local.State machine) →
  (scanned : Local.Symbol machine) →
  Interpreter.fetchConcreteRuleWork machine q scanned
    ≤ Selector.RuleWidth machine
executeSelectedWindowFetchBound machine q scanned =
  Interpreter.fetchConcreteRuleWorkBound machine q scanned

------------------------------------------------------------------------
-- MAX-CUT STATUS
--
-- PAID:
-- * literal sequential selection from ConcreteTapeMachine.rules;
-- * successful selection produces a full TapeRow, not only a rule record;
-- * produced row carries an actual Local.MachineStep witness;
-- * operational lookup cost is the same finite rule-width seen by Cook--Levin.
--
-- OPEN:
-- * canonical parsing of an arbitrary well-formed TapeRow into the unique
--   headed local window, including blank extension at the finite boundary;
-- * iteration of executeSelectedWindow on that canonical row representation;
-- * standard TM <-> ConcreteTapeMachine polynomial simulations;
-- * transport of polynomial running time through those simulations;
-- * universal SAT lower-bound obstruction.
------------------------------------------------------------------------
