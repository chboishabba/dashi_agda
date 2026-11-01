module DASHI.Mathematics.Complexity.ConcreteTapeLegalWindowBoolExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeLocalWindowPatternsExact as Pattern

andBool : Bool → Bool → Bool
andBool false right = false
andBool true right = right

all3 : Bool → Bool → Bool → Bool
all3 a b c = andBool a (andBool b c)

all4 : Bool → Bool → Bool → Bool → Bool
all4 a b c d = andBool a (andBool b (andBool c d))

all5 : Bool → Bool → Bool → Bool → Bool → Bool
all5 a b c d e =
  andBool a (andBool b (andBool c (andBool d e)))

all6 : Bool → Bool → Bool → Bool → Bool → Bool → Bool
all6 a b c d e f =
  andBool a (andBool b (andBool c (andBool d (andBool e f))))

stateEq :
  (machine : Local.ConcreteTapeMachine) →
  Local.State machine →
  Local.State machine →
  Bool
stateEq machine =
  Local.decideEqual (Local.finiteState machine)

symbolEq :
  (machine : Local.ConcreteTapeMachine) →
  Local.Symbol machine →
  Local.Symbol machine →
  Bool
symbolEq machine =
  Local.decideEqual (Local.finiteSymbol machine)

legalWindowBool :
  (machine : Local.ConcreteTapeMachine) →
  Local.TapeRule (Local.State machine) (Local.Symbol machine) →
  Local.SixCellWindow machine →
  Bool

legalWindowBool machine rule
    (Local.six-cell-window
      (Local.plain a) (Local.plain b) (Local.plain c)
      (Local.plain a') (Local.plain b') (Local.plain c')) =
  all3
    (symbolEq machine a a')
    (symbolEq machine b b')
    (symbolEq machine c c')

legalWindowBool machine
    (Local.tape-rule q a q' b Local.moveLeft)
    (Local.six-cell-window
      (Local.plain left) (Local.headed oldQ oldA) (Local.plain right)
      (Local.headed newQ newLeft) (Local.plain newB) (Local.plain newRight)) =
  all6
    (stateEq machine oldQ q)
    (symbolEq machine oldA a)
    (stateEq machine newQ q')
    (symbolEq machine newLeft left)
    (symbolEq machine newB b)
    (symbolEq machine newRight right)

legalWindowBool machine
    (Local.tape-rule q a q' b Local.moveLeft)
    (Local.six-cell-window
      (Local.plain first) (Local.plain second) (Local.plain left)
      (Local.plain first') (Local.plain second') (Local.headed newQ newLeft)) =
  all5
    (symbolEq machine first first')
    (symbolEq machine second second')
    (stateEq machine newQ q')
    (symbolEq machine newLeft left)
    (symbolEq machine left left)

legalWindowBool machine
    (Local.tape-rule q a q' b Local.moveLeft)
    (Local.six-cell-window
      (Local.plain context) (Local.plain left) (Local.headed oldQ oldA)
      (Local.plain context') (Local.headed newQ newLeft) (Local.plain newB)) =
  all6
    (symbolEq machine context context')
    (stateEq machine oldQ q)
    (symbolEq machine oldA a)
    (stateEq machine newQ q')
    (symbolEq machine newLeft left)
    (symbolEq machine newB b)

legalWindowBool machine
    (Local.tape-rule q a q' b Local.moveLeft)
    (Local.six-cell-window
      (Local.headed oldQ oldA) (Local.plain right) (Local.plain context)
      (Local.plain newB) (Local.plain right') (Local.plain context')) =
  all6
    (stateEq machine oldQ q)
    (symbolEq machine oldA a)
    (symbolEq machine newB b)
    (symbolEq machine right right')
    (symbolEq machine context context')
    (symbolEq machine right right)

legalWindowBool machine
    (Local.tape-rule q a q' b Local.stayPut)
    (Local.six-cell-window
      (Local.plain left) (Local.headed oldQ oldA) (Local.plain right)
      (Local.plain left') (Local.headed newQ newB) (Local.plain right')) =
  all6
    (symbolEq machine left left')
    (stateEq machine oldQ q)
    (symbolEq machine oldA a)
    (stateEq machine newQ q')
    (symbolEq machine newB b)
    (symbolEq machine right right')

legalWindowBool machine
    (Local.tape-rule q a q' b Local.stayPut)
    (Local.six-cell-window
      (Local.plain context) (Local.plain left) (Local.headed oldQ oldA)
      (Local.plain context') (Local.plain left') (Local.headed newQ newB)) =
  all6
    (symbolEq machine context context')
    (symbolEq machine left left')
    (stateEq machine oldQ q)
    (symbolEq machine oldA a)
    (stateEq machine newQ q')
    (symbolEq machine newB b)

legalWindowBool machine
    (Local.tape-rule q a q' b Local.stayPut)
    (Local.six-cell-window
      (Local.headed oldQ oldA) (Local.plain right) (Local.plain context)
      (Local.headed newQ newB) (Local.plain right') (Local.plain context')) =
  all6
    (stateEq machine oldQ q)
    (symbolEq machine oldA a)
    (stateEq machine newQ q')
    (symbolEq machine newB b)
    (symbolEq machine right right')
    (symbolEq machine context context')

legalWindowBool machine
    (Local.tape-rule q a q' b Local.moveRight)
    (Local.six-cell-window
      (Local.plain left) (Local.headed oldQ oldA) (Local.plain right)
      (Local.plain left') (Local.plain newB) (Local.headed newQ newRight)) =
  all6
    (symbolEq machine left left')
    (stateEq machine oldQ q)
    (symbolEq machine oldA a)
    (symbolEq machine newB b)
    (stateEq machine newQ q')
    (symbolEq machine newRight right)

legalWindowBool machine
    (Local.tape-rule q a q' b Local.moveRight)
    (Local.six-cell-window
      (Local.plain context) (Local.plain left) (Local.headed oldQ oldA)
      (Local.plain context') (Local.plain left') (Local.plain newB)) =
  all6
    (symbolEq machine context context')
    (symbolEq machine left left')
    (stateEq machine oldQ q)
    (symbolEq machine oldA a)
    (symbolEq machine newB b)
    (symbolEq machine left left)

legalWindowBool machine
    (Local.tape-rule q a q' b Local.moveRight)
    (Local.six-cell-window
      (Local.headed oldQ oldA) (Local.plain right) (Local.plain context)
      (Local.plain newB) (Local.headed newQ newRight) (Local.plain context')) =
  all6
    (stateEq machine oldQ q)
    (symbolEq machine oldA a)
    (symbolEq machine newB b)
    (stateEq machine newQ q')
    (symbolEq machine newRight right)
    (symbolEq machine context context')

legalWindowBool machine
    (Local.tape-rule q a q' b Local.moveRight)
    (Local.six-cell-window
      (Local.plain right) (Local.plain first) (Local.plain second)
      (Local.headed newQ newRight) (Local.plain first') (Local.plain second')) =
  all5
    (stateEq machine newQ q')
    (symbolEq machine newRight right)
    (symbolEq machine first first')
    (symbolEq machine second second')
    (symbolEq machine right right)

legalWindowBool machine rule window = false

semanticLegalImpliesBooleanTrue :
  ∀ {machine rule window} →
  Pattern.LegalWindowForRule machine rule window →
  legalWindowBool machine rule window ≡ true
semanticLegalImpliesBooleanTrue {machine} Pattern.legal-unchanged
    rewrite Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _ =
  refl
semanticLegalImpliesBooleanTrue {machine}
    (Pattern.legal-centered Local.realizes-left)
    rewrite Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _ =
  refl
semanticLegalImpliesBooleanTrue {machine}
    (Pattern.legal-centered Local.realizes-stay)
    rewrite Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _ =
  refl
semanticLegalImpliesBooleanTrue {machine}
    (Pattern.legal-centered Local.realizes-right)
    rewrite Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _ =
  refl
semanticLegalImpliesBooleanTrue {machine} Pattern.left-overlap-minus-two
    rewrite Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _ =
  refl
semanticLegalImpliesBooleanTrue {machine} Pattern.left-overlap-minus-one
    rewrite Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _ =
  refl
semanticLegalImpliesBooleanTrue {machine} Pattern.left-overlap-plus-one
    rewrite Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _ =
  refl
semanticLegalImpliesBooleanTrue {machine} Pattern.stay-overlap-minus-one
    rewrite Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _ =
  refl
semanticLegalImpliesBooleanTrue {machine} Pattern.stay-overlap-plus-one
    rewrite Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _ =
  refl
semanticLegalImpliesBooleanTrue {machine} Pattern.right-overlap-minus-one
    rewrite Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _ =
  refl
semanticLegalImpliesBooleanTrue {machine} Pattern.right-overlap-plus-one
    rewrite Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _ =
  refl
semanticLegalImpliesBooleanTrue {machine} Pattern.right-overlap-plus-two
    rewrite Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _ =
  refl

record ConcreteTapeLegalWindowBoolBoundary : Set where
  constructor concrete-tape-legal-window-bool-boundary
  field
    reflectedStateEqualityReused : Bool
    reflectedSymbolEqualityReused : Bool
    totalBooleanRecognizerPaid : Bool
    semanticToBooleanReflectionPaid : Bool
    booleanToSemanticReflectionPaid : Bool
    fullBooleanIffPaid : Bool
    canonicalSATWeldPaid : Bool
    runToSATPaid : Bool
    genericCookLevinPaid : Bool
    pVsNPResolved : Bool

canonicalConcreteTapeLegalWindowBoolBoundary :
  ConcreteTapeLegalWindowBoolBoundary
canonicalConcreteTapeLegalWindowBoolBoundary =
  concrete-tape-legal-window-bool-boundary
    true true true true false false false false false false
