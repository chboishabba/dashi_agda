module DASHI.Mathematics.Complexity.ConcreteTapeLocalWindowPatternsExact where

------------------------------------------------------------------------
-- COMPLETE DIRECTIONAL 2x3 WINDOW GRAMMAR FOR ONE TAPE STEP
--
-- For a unique-head one-tape transition, every sliding width-three window is
-- unchanged or one of the finite directional overlap patterns. This original
-- grammar is indexed by the SAME rule, not parameterised by one fixed rule.
-- Local legality ALONE does not force a globally unique post-step head:
-- a row-boundary overlap can introduce a phantom head. The guarded global
-- reconstruction must establish an additional source-owned endcap invariant.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local

data LegalWindowForRule
    (machine : Local.ConcreteTapeMachine) :
    Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine) →
    Local.SixCellWindow machine → Set where

  legal-unchanged :
    ∀ {rule firstSymbol secondSymbol thirdSymbol} →
    LegalWindowForRule machine rule
      (Local.six-cell-window
        (Local.plain firstSymbol)
        (Local.plain secondSymbol)
        (Local.plain thirdSymbol)
        (Local.plain firstSymbol)
        (Local.plain secondSymbol)
        (Local.plain thirdSymbol))

  legal-centered :
    ∀ {rule window} →
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


data IsPlainCell {State Symbol : Set} :
    Local.TapeCell State Symbol → Set where
  is-plain : ∀ {symbol} → IsPlainCell (Local.plain symbol)

-- Old-left-plain alone does NOT imply new-left-plain: realizes-left
-- and right-overlap-plus-two can introduce a head. Symmetrically
-- realizes-right and left-overlap-minus-two can head the right cell.
-- These classifications preserve exactly those cases, rather than
-- deriving the previously false universal plain-cell invariants.

data IsHeadCell {State Symbol : Set} :
    Local.TapeCell State Symbol → Set where
  is-headed : ∀ {state symbol} →
    IsHeadCell (Local.headed state symbol)

open import Data.Sum using (_⊎_; inj₁; inj₂)

legalPlainTripleNewLeftClassified :
  ∀ {machine rule first second third newLeft newCenter newRight} →
  LegalWindowForRule machine rule
    (Local.six-cell-window
      (Local.plain first) (Local.plain second) (Local.plain third)
      newLeft newCenter newRight) →
  IsPlainCell newLeft ⊎ IsHeadCell newLeft
legalPlainTripleNewLeftClassified legal-unchanged = inj₁ is-plain
legalPlainTripleNewLeftClassified left-overlap-minus-two = inj₁ is-plain
legalPlainTripleNewLeftClassified right-overlap-plus-two = inj₂ is-headed

legalPlainTripleNewRightClassified :
  ∀ {machine rule first second third newLeft newCenter newRight} →
  LegalWindowForRule machine rule
    (Local.six-cell-window
      (Local.plain first) (Local.plain second) (Local.plain third)
      newLeft newCenter newRight) →
  IsPlainCell newRight ⊎ IsHeadCell newRight
legalPlainTripleNewRightClassified legal-unchanged = inj₁ is-plain
legalPlainTripleNewRightClassified left-overlap-minus-two = inj₂ is-headed
legalPlainTripleNewRightClassified right-overlap-plus-two = inj₁ is-plain

-- The actual proof boundary used by prefix/suffix propagation:
-- once one new boundary cell is plain, a legal *all-plain old*
-- triple cannot spontaneously change the adjacent new middle cell
-- into a head; the only two all-plain exceptional overlap windows
-- place their potential new head at one OUTER edge.
legalPlainTripleNewLeftPlainForcesMiddlePlain :
  ∀ {machine rule first second third newLeft newCenter newRight} →
  LegalWindowForRule machine rule
    (Local.six-cell-window
      (Local.plain first) (Local.plain second) (Local.plain third)
      newLeft newCenter newRight) →
  IsPlainCell newLeft → IsPlainCell newCenter
legalPlainTripleNewLeftPlainForcesMiddlePlain legal-unchanged is-plain =
  is-plain
legalPlainTripleNewLeftPlainForcesMiddlePlain left-overlap-minus-two
    is-plain = is-plain
legalPlainTripleNewLeftPlainForcesMiddlePlain right-overlap-plus-two ()

legalPlainTripleNewRightPlainForcesMiddlePlain :
  ∀ {machine rule first second third newLeft newCenter newRight} →
  LegalWindowForRule machine rule
    (Local.six-cell-window
      (Local.plain first) (Local.plain second) (Local.plain third)
      newLeft newCenter newRight) →
  IsPlainCell newRight → IsPlainCell newCenter
legalPlainTripleNewRightPlainForcesMiddlePlain legal-unchanged is-plain =
  is-plain
legalPlainTripleNewRightPlainForcesMiddlePlain left-overlap-minus-two ()
legalPlainTripleNewRightPlainForcesMiddlePlain right-overlap-plus-two
    is-plain = is-plain

configuredOldLeftPlain :
  ∀ {machine rule window} →
  Local.RuleRealizesWindow machine rule window →
  IsPlainCell (Local.oldLeft window)
configuredOldLeftPlain Local.realizes-left = is-plain
configuredOldLeftPlain Local.realizes-stay = is-plain
configuredOldLeftPlain Local.realizes-right = is-plain

configuredOldRightPlain :
  ∀ {machine rule window} →
  Local.RuleRealizesWindow machine rule window →
  IsPlainCell (Local.oldRight window)
configuredOldRightPlain Local.realizes-left = is-plain
configuredOldRightPlain Local.realizes-stay = is-plain
configuredOldRightPlain Local.realizes-right = is-plain

------------------------------------------------------------------------
-- One-cell end guards. These express genuine missing tableau premises,
-- not an assumption that the *whole* post-transition context is plain.
-- FrontPlain is vacuous for []; EndPlain requires a plain final cell
-- on nonempty lists. They are only boundary conditions on the exact
-- after-prefix and after-suffix lists extracted at the centered window.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)

data FrontPlain {State Symbol : Set} :
    List (Local.TapeCell State Symbol) → Set where
  frontNil : FrontPlain []
  frontCons :
    ∀ {symbol rest} →
    FrontPlain (Local.plain symbol ∷ rest)

data EndPlain {State Symbol : Set} :
    List (Local.TapeCell State Symbol) → Set where
  endNil : EndPlain []
  endOne :
    ∀ {symbol} →
    EndPlain (Local.plain symbol ∷ [])
  endMore :
    ∀ {first second rest} →
    EndPlain (second ∷ rest) →
    EndPlain (first ∷ second ∷ rest)

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
