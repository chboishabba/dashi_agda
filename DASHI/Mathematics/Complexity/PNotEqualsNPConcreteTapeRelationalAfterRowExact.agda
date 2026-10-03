module DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRelationalAfterRowExact where

------------------------------------------------------------------------
-- RELATIONAL AFTER ROW = EXECUTABLE CANONICAL AFTER ROW
--
-- A WellFormedMachineStep already contains a literal WindowRewriteOccurrence.
-- Its `afterShape` field says that the relational output row is exactly the
-- common prefix, the configured new three-cell window, and the common suffix.
-- `afterRowForRule` is defined by the same three directional windows.
--
-- Hence, after case-splitting on the genuine RuleRealizesWindow witness, the
-- remaining equality is only injectivity of the one-field TapeRow record.
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
-- Exact row-level converse seam.
------------------------------------------------------------------------

relationalAfterRowEqualsExecutableAfterRow :
  ∀ {machine before after}
    (wellFormed : WF.WellFormedMachineStep machine before after) →
  let step = WF.step wellFormed
      occurrence = WF.occurrence (WF.wellFormedOccurrence wellFormed)
  in
  after ≡
    Window.afterRowForRule
      machine
      (Local.prefix occurrence)
      _
      _
      (Local.suffix occurrence)
      (Local.rule step)
relationalAfterRowEqualsExecutableAfterRow wellFormed
    with Local.ruleIsConfigured (WF.step wellFormed)
... | Local.realizes-left
      {leftSymbol = left} {rightSymbol = right} =
  tapeRowCellsInjective
    (Local.afterShape
      (WF.occurrence (WF.wellFormedOccurrence wellFormed)))
... | Local.realizes-stay
      {leftSymbol = left} {rightSymbol = right} =
  tapeRowCellsInjective
    (Local.afterShape
      (WF.occurrence (WF.wellFormedOccurrence wellFormed)))
... | Local.realizes-right
      {leftSymbol = left} {rightSymbol = right} =
  tapeRowCellsInjective
    (Local.afterShape
      (WF.occurrence (WF.wellFormedOccurrence wellFormed)))

------------------------------------------------------------------------
-- A more explicit projection form is useful downstream: the two anonymous
-- symbol arguments above are definitionally the old left/right plain cells
-- exposed by the directional realization witness.
------------------------------------------------------------------------

relationalAfterCellsEqualsExecutableAfterCells :
  ∀ {machine before after}
    (wellFormed : WF.WellFormedMachineStep machine before after) →
  let step = WF.step wellFormed
      occurrence = WF.occurrence (WF.wellFormedOccurrence wellFormed)
  in
  Local.cells after ≡
    Local.cells
      (Window.afterRowForRule
        machine
        (Local.prefix occurrence)
        _
        _
        (Local.suffix occurrence)
        (Local.rule step))
relationalAfterCellsEqualsExecutableAfterCells wellFormed =
  case relationalAfterRowEqualsExecutableAfterRow wellFormed of λ where
    refl → refl

------------------------------------------------------------------------
-- MAX-CUT STATUS
--
-- PAID IN THIS OWNER:
-- * exact dependent row equality between every relational well-formed output
--   and `Window.afterRowForRule` for the same literal occurrence and rule;
-- * no synthetic transition carrier and no change to machine semantics.
--
-- Together with PNotEqualsNPConcreteTapeRelationalRuleAgreementExact:
-- * relational step -> executable lookup succeeds;
-- * RuleDispatchUnique -> selected executable rule = relational rule;
-- * this file -> selected executable output row = relational output row.
--
-- NEXT:
-- * package the two equalities into the extensional execute<->relational iff;
-- * then freeze local semantics and pay standard deterministic-TM polynomial
--   simulation/clock transport.
------------------------------------------------------------------------
