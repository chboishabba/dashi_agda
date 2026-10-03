module DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRelationalAfterRowExact where

------------------------------------------------------------------------
-- RELATIONAL AFTER ROW = EXECUTABLE CANONICAL AFTER ROW
--
-- A WellFormedMachineStep already contains a literal WindowRewriteOccurrence.
-- Its `afterShape` field says that the relational output row is exactly the
-- common prefix, the configured new three-cell window, and the common suffix.
-- `afterRowForRule` is defined by the same three directional windows.
--
-- We first extract the executable after-row by pattern matching the genuine
-- RuleRealizesWindow witness.  Then `afterShape` gives exact row equality.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeExecutableWindowStepExact as Window

------------------------------------------------------------------------
-- TapeRow has exactly one data field, so equality of cells is row equality.
------------------------------------------------------------------------

tapeRowCellsInjective :
  ∀ {machine : Local.ConcreteTapeMachine}
    {left right : Local.TapeRow machine} →
  Local.cells left ≡ Local.cells right →
  left ≡ right
tapeRowCellsInjective {left = Local.tape-row xs} {right = Local.tape-row .xs} refl = refl

------------------------------------------------------------------------
-- Canonical executable row extracted from a relational well-formed step.
------------------------------------------------------------------------

relationalExecutableAfter :
  ∀ {machine before after} →
  WF.WellFormedMachineStep machine before after →
  Local.TapeRow machine
relationalExecutableAfter {machine} wellFormed
    with Local.ruleIsConfigured (WF.step wellFormed)
... | Local.realizes-left
      {leftSymbol = left} {rightSymbol = right} =
  Window.afterRowForRule
    machine
    (Local.prefix occurrence)
    left right
    (Local.suffix occurrence)
    (Local.rule (WF.step wellFormed))
  where
    occurrence = WF.occurrence (WF.wellFormedOccurrence wellFormed)
... | Local.realizes-stay
      {leftSymbol = left} {rightSymbol = right} =
  Window.afterRowForRule
    machine
    (Local.prefix occurrence)
    left right
    (Local.suffix occurrence)
    (Local.rule (WF.step wellFormed))
  where
    occurrence = WF.occurrence (WF.wellFormedOccurrence wellFormed)
... | Local.realizes-right
      {leftSymbol = left} {rightSymbol = right} =
  Window.afterRowForRule
    machine
    (Local.prefix occurrence)
    left right
    (Local.suffix occurrence)
    (Local.rule (WF.step wellFormed))
  where
    occurrence = WF.occurrence (WF.wellFormedOccurrence wellFormed)

------------------------------------------------------------------------
-- Exact row-level converse seam.
------------------------------------------------------------------------

relationalAfterRowEqualsExecutableAfterRow :
  ∀ {machine before after}
    (wellFormed : WF.WellFormedMachineStep machine before after) →
  after ≡ relationalExecutableAfter wellFormed
relationalAfterRowEqualsExecutableAfterRow wellFormed
    with Local.ruleIsConfigured (WF.step wellFormed)
... | Local.realizes-left =
  tapeRowCellsInjective
    (Local.afterShape
      (WF.occurrence (WF.wellFormedOccurrence wellFormed)))
... | Local.realizes-stay =
  tapeRowCellsInjective
    (Local.afterShape
      (WF.occurrence (WF.wellFormedOccurrence wellFormed)))
... | Local.realizes-right =
  tapeRowCellsInjective
    (Local.afterShape
      (WF.occurrence (WF.wellFormedOccurrence wellFormed)))

relationalAfterCellsEqualsExecutableAfterCells :
  ∀ {machine before after}
    (wellFormed : WF.WellFormedMachineStep machine before after) →
  Local.cells after ≡ Local.cells (relationalExecutableAfter wellFormed)
relationalAfterCellsEqualsExecutableAfterCells wellFormed
    with relationalAfterRowEqualsExecutableAfterRow wellFormed
... | refl = refl

------------------------------------------------------------------------
-- MAX-CUT STATUS
--
-- PAID IN THIS OWNER:
-- * the directional realization witness determines the exact executable
--   `afterRowForRule` on the relational occurrence's prefix/suffix;
-- * every relational well-formed output row equals that canonical executable
--   row exactly;
-- * no synthetic transition carrier and no change to machine semantics.
--
-- Together with PNotEqualsNPConcreteTapeRelationalRuleAgreementExact:
-- * relational step -> executable lookup succeeds;
-- * RuleDispatchUnique -> selected executable rule = relational rule;
-- * this file -> selected executable output row = relational output row.
--
-- NEXT:
-- * package these into the extensional execute<->relational theorem;
-- * then freeze local semantics and pay standard deterministic-TM polynomial
--   simulation/clock transport.
------------------------------------------------------------------------
