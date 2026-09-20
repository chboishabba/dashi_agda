module DASHI.Mathematics.Complexity.ConcreteTapeLocalWindowPatternsExact where

------------------------------------------------------------------------
-- COMPLETE DIRECTIONAL 2x3 WINDOW GRAMMAR FOR ONE TAPE STEP
--
-- For a unique-head one-tape transition, every sliding width-three window is
-- either unchanged or one of the finite overlap patterns below.  This module
-- pays the fixed-width semantic grammar; the remaining theorem is the global
-- scan showing that every window of a well-formed rewrite belongs to it, and
-- conversely that a globally compatible scan reconstructs one rewrite.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local

data LegalWindowForRule
    (machine : Local.ConcreteTapeMachine)
    (rule : Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine)) :
    Local.SixCellWindow machine → Set where

  legal-unchanged :
    ∀ {firstSymbol secondSymbol thirdSymbol} →
    LegalWindowForRule machine rule
      (Local.six-cell-window
        (Local.plain firstSymbol)
        (Local.plain secondSymbol)
        (Local.plain thirdSymbol)
        (Local.plain firstSymbol)
        (Local.plain secondSymbol)
        (Local.plain thirdSymbol))

  legal-centered :
    ∀ {window} →
    Local.RuleRealizesWindow machine rule window →
    LegalWindowForRule machine rule window

  left-overlap-minus-two :
    ∀ {q q' a b first second leftSymbol} →
    LegalWindowForRule machine
      (Local.tape-rule q a q' b Local.moveLeft)
      (Local.six-cell-window
        (Local.plain first)
        (Local.plain second)
        (Local.plain leftSymbol)
        (Local.plain first)
        (Local.plain second)
        (Local.headed q' leftSymbol))

  left-overlap-minus-one :
    ∀ {q q' a b context leftSymbol} →
    LegalWindowForRule machine
      (Local.tape-rule q a q' b Local.moveLeft)
      (Local.six-cell-window
        (Local.plain context)
        (Local.plain leftSymbol)
        (Local.headed q a)
        (Local.plain context)
        (Local.headed q' leftSymbol)
        (Local.plain b))

  left-overlap-plus-one :
    ∀ {q q' a b rightSymbol context} →
    LegalWindowForRule machine
      (Local.tape-rule q a q' b Local.moveLeft)
      (Local.six-cell-window
        (Local.headed q a)
        (Local.plain rightSymbol)
        (Local.plain context)
        (Local.plain b)
        (Local.plain rightSymbol)
        (Local.plain context))

  stay-overlap-minus-one :
    ∀ {q q' a b context leftSymbol} →
    LegalWindowForRule machine
      (Local.tape-rule q a q' b Local.stayPut)
      (Local.six-cell-window
        (Local.plain context)
        (Local.plain leftSymbol)
        (Local.headed q a)
        (Local.plain context)
        (Local.plain leftSymbol)
        (Local.headed q' b))

  stay-overlap-plus-one :
    ∀ {q q' a b rightSymbol context} →
    LegalWindowForRule machine
      (Local.tape-rule q a q' b Local.stayPut)
      (Local.six-cell-window
        (Local.headed q a)
        (Local.plain rightSymbol)
        (Local.plain context)
        (Local.headed q' b)
        (Local.plain rightSymbol)
        (Local.plain context))

  right-overlap-minus-one :
    ∀ {q q' a b context leftSymbol} →
    LegalWindowForRule machine
      (Local.tape-rule q a q' b Local.moveRight)
      (Local.six-cell-window
        (Local.plain context)
        (Local.plain leftSymbol)
        (Local.headed q a)
        (Local.plain context)
        (Local.plain leftSymbol)
        (Local.plain b))

  right-overlap-plus-one :
    ∀ {q q' a b rightSymbol context} →
    LegalWindowForRule machine
      (Local.tape-rule q a q' b Local.moveRight)
      (Local.six-cell-window
        (Local.headed q a)
        (Local.plain rightSymbol)
        (Local.plain context)
        (Local.plain b)
        (Local.headed q' rightSymbol)
        (Local.plain context))

  right-overlap-plus-two :
    ∀ {q q' a b rightSymbol first second} →
    LegalWindowForRule machine
      (Local.tape-rule q a q' b Local.moveRight)
      (Local.six-cell-window
        (Local.plain rightSymbol)
        (Local.plain first)
        (Local.plain second)
        (Local.headed q' rightSymbol)
        (Local.plain first)
        (Local.plain second))

realizedCentralWindowIsLegal :
  ∀ {machine rule window} →
  Local.RuleRealizesWindow machine rule window →
  LegalWindowForRule machine rule window
realizedCentralWindowIsLegal =
  legal-centered


legalPlainLeftSymbolAgreement :
  ∀ {machine rule oldSymbol newSymbol oldCenter oldRight newCenter newRight} →
  LegalWindowForRule machine rule
    (Local.six-cell-window
      (Local.plain oldSymbol) oldCenter oldRight
      (Local.plain newSymbol) newCenter newRight) →
  oldSymbol ≡ newSymbol
legalPlainLeftSymbolAgreement legal-unchanged = refl
legalPlainLeftSymbolAgreement
    (legal-centered Local.realizes-stay) = refl
legalPlainLeftSymbolAgreement
    (legal-centered Local.realizes-right) = refl
legalPlainLeftSymbolAgreement left-overlap-minus-two = refl
legalPlainLeftSymbolAgreement left-overlap-minus-one = refl
legalPlainLeftSymbolAgreement stay-overlap-minus-one = refl
legalPlainLeftSymbolAgreement right-overlap-minus-one = refl


legalPlainRightSymbolAgreement :
  ∀ {machine rule oldLeft oldCenter oldSymbol newLeft newCenter newSymbol} →
  LegalWindowForRule machine rule
    (Local.six-cell-window
      oldLeft oldCenter (Local.plain oldSymbol)
      newLeft newCenter (Local.plain newSymbol)) →
  oldSymbol ≡ newSymbol
legalPlainRightSymbolAgreement legal-unchanged = refl
legalPlainRightSymbolAgreement
    (legal-centered Local.realizes-left) = refl
legalPlainRightSymbolAgreement
    (legal-centered Local.realizes-stay) = refl
legalPlainRightSymbolAgreement left-overlap-plus-one = refl
legalPlainRightSymbolAgreement stay-overlap-plus-one = refl
legalPlainRightSymbolAgreement right-overlap-plus-one = refl
legalPlainRightSymbolAgreement right-overlap-plus-two = refl

record ConcreteTapeLocalWindowPatternsBoundary : Set where
  constructor concrete-tape-local-window-patterns-boundary
  field
    unchangedWindowPatternPaid : Bool
    centeredRuleWindowPatternPaid : Bool
    leftMoveOverlapPatternsPaid : Bool
    stayMoveOverlapPatternsPaid : Bool
    rightMoveOverlapPatternsPaid : Bool
    completeDirectionalOverlapPatternGrammarPaid : Bool
    wholeRowAllWindowScanPaid : Bool
    reverseScanToUniqueRewritePaid : Bool
    canonicalSATBooleanPredicateWeldPaid : Bool
    pVsNPResolved : Bool

canonicalConcreteTapeLocalWindowPatternsBoundary :
  ConcreteTapeLocalWindowPatternsBoundary
canonicalConcreteTapeLocalWindowPatternsBoundary =
  concrete-tape-local-window-patterns-boundary
    true true true true true true false false false false
