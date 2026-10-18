module DASHI.Mathematics.Complexity.ConcreteTapeLegalWindowReflectionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeLocalWindowPatternsExact as Pattern
import DASHI.Mathematics.Complexity.ConcreteTapeLegalWindowBoolExact as BoolRec

stateEqTrue :
  ∀ {machine x y} →
  BoolRec.stateEq machine x y ≡ true →
  x ≡ y
stateEqTrue {machine} =
  Local.decideEqualSound (Local.finiteState machine)

symbolEqTrue :
  ∀ {machine x y} →
  BoolRec.symbolEq machine x y ≡ true →
  x ≡ y
symbolEqTrue {machine} =
  Local.decideEqualSound (Local.finiteSymbol machine)

data LegalWindowRecognition
    (machine : Local.ConcreteTapeMachine)
    (rule : Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine))
    (window : Local.SixCellWindow machine) : Set where
  rejected :
    LegalWindowRecognition machine rule window

  accepted :
    Pattern.LegalWindowForRule machine rule window →
    LegalWindowRecognition machine rule window

recognitionBool :
  ∀ {machine rule window} →
  LegalWindowRecognition machine rule window →
  Bool
recognitionBool rejected = false
recognitionBool (accepted legal) = true

all3True :
  ∀ a b c →
  BoolRec.all3 a b c ≡ true →
  (a ≡ true) × (b ≡ true) × (c ≡ true)
all3True true true true refl =
  refl , (refl , refl)
all3True false b c ()
all3True true false c ()
all3True true true false ()

all5True :
  ∀ a b c d e →
  BoolRec.all5 a b c d e ≡ true →
  (a ≡ true) × (b ≡ true) × (c ≡ true) ×
  (d ≡ true) × (e ≡ true)
all5True true true true true true refl =
  refl , (refl , (refl , (refl , refl)))
all5True false b c d e ()
all5True true false c d e ()
all5True true true false d e ()
all5True true true true false e ()
all5True true true true true false ()

all6True :
  ∀ a b c d e f →
  BoolRec.all6 a b c d e f ≡ true →
  (a ≡ true) × (b ≡ true) × (c ≡ true) ×
  (d ≡ true) × (e ≡ true) × (f ≡ true)
all6True true true true true true true refl =
  refl , (refl , (refl , (refl , (refl , refl))))
all6True false b c d e f ()
all6True true false c d e f ()
all6True true true false d e f ()
all6True true true true false e f ()
all6True true true true true false f ()
all6True true true true true true false ()

recognizeLegalWindow :
  (machine : Local.ConcreteTapeMachine) →
  (rule : Local.TapeRule
    (Local.State machine)
    (Local.Symbol machine)) →
  (window : Local.SixCellWindow machine) →
  LegalWindowRecognition machine rule window

recognizeLegalWindow machine rule
    (Local.six-cell-window
      (Local.plain a) (Local.plain b) (Local.plain c)
      (Local.plain a') (Local.plain b') (Local.plain c'))
    with BoolRec.all3
      (BoolRec.symbolEq machine a a')
      (BoolRec.symbolEq machine b b')
      (BoolRec.symbolEq machine c c')
... | false = rejected
... | true
    with all3True
      (BoolRec.symbolEq machine a a')
      (BoolRec.symbolEq machine b b')
      (BoolRec.symbolEq machine c c')
      refl
... | ea , (eb , ec)
    with symbolEqTrue ea | symbolEqTrue eb | symbolEqTrue ec
... | refl | refl | refl =
  accepted Pattern.legal-unchanged

recognizeLegalWindow machine
    (Local.tape-rule q a q' b Local.moveLeft)
    (Local.six-cell-window
      (Local.plain left) (Local.headed oldQ oldA) (Local.plain right)
      (Local.headed newQ newLeft) (Local.plain newB) (Local.plain newRight))
    with BoolRec.all6
      (BoolRec.stateEq machine oldQ q)
      (BoolRec.symbolEq machine oldA a)
      (BoolRec.stateEq machine newQ q')
      (BoolRec.symbolEq machine newLeft left)
      (BoolRec.symbolEq machine newB b)
      (BoolRec.symbolEq machine newRight right)
... | false = rejected
... | true
    with all6True
      (BoolRec.stateEq machine oldQ q)
      (BoolRec.symbolEq machine oldA a)
      (BoolRec.stateEq machine newQ q')
      (BoolRec.symbolEq machine newLeft left)
      (BoolRec.symbolEq machine newB b)
      (BoolRec.symbolEq machine newRight right)
      refl
... | e1 , (e2 , (e3 , (e4 , (e5 , e6))))
    with stateEqTrue e1 | symbolEqTrue e2 | stateEqTrue e3
       | symbolEqTrue e4 | symbolEqTrue e5 | symbolEqTrue e6
... | refl | refl | refl | refl | refl | refl =
  accepted (Pattern.legal-centered Local.realizes-left)

recognizeLegalWindow machine
    (Local.tape-rule q a q' b Local.stayPut)
    (Local.six-cell-window
      (Local.plain left) (Local.headed oldQ oldA) (Local.plain right)
      (Local.plain left') (Local.headed newQ newB) (Local.plain right'))
    with BoolRec.all6
      (BoolRec.symbolEq machine left left')
      (BoolRec.stateEq machine oldQ q)
      (BoolRec.symbolEq machine oldA a)
      (BoolRec.stateEq machine newQ q')
      (BoolRec.symbolEq machine newB b)
      (BoolRec.symbolEq machine right right')
... | false = rejected
... | true
    with all6True
      (BoolRec.symbolEq machine left left')
      (BoolRec.stateEq machine oldQ q)
      (BoolRec.symbolEq machine oldA a)
      (BoolRec.stateEq machine newQ q')
      (BoolRec.symbolEq machine newB b)
      (BoolRec.symbolEq machine right right')
      refl
... | e1 , (e2 , (e3 , (e4 , (e5 , e6))))
    with symbolEqTrue e1 | stateEqTrue e2 | symbolEqTrue e3
       | stateEqTrue e4 | symbolEqTrue e5 | symbolEqTrue e6
... | refl | refl | refl | refl | refl | refl =
  accepted (Pattern.legal-centered Local.realizes-stay)

recognizeLegalWindow machine
    (Local.tape-rule q a q' b Local.moveRight)
    (Local.six-cell-window
      (Local.plain left) (Local.headed oldQ oldA) (Local.plain right)
      (Local.plain left') (Local.plain newB) (Local.headed newQ newRight))
    with BoolRec.all6
      (BoolRec.symbolEq machine left left')
      (BoolRec.stateEq machine oldQ q)
      (BoolRec.symbolEq machine oldA a)
      (BoolRec.symbolEq machine newB b)
      (BoolRec.stateEq machine newQ q')
      (BoolRec.symbolEq machine newRight right)
... | false = rejected
... | true
    with all6True
      (BoolRec.symbolEq machine left left')
      (BoolRec.stateEq machine oldQ q)
      (BoolRec.symbolEq machine oldA a)
      (BoolRec.symbolEq machine newB b)
      (BoolRec.stateEq machine newQ q')
      (BoolRec.symbolEq machine newRight right)
      refl
... | e1 , (e2 , (e3 , (e4 , (e5 , e6))))
    with symbolEqTrue e1 | stateEqTrue e2 | symbolEqTrue e3
       | symbolEqTrue e4 | stateEqTrue e5 | symbolEqTrue e6
... | refl | refl | refl | refl | refl | refl =
  accepted (Pattern.legal-centered Local.realizes-right)

recognizeLegalWindow machine
    (Local.tape-rule q a q' b Local.moveLeft)
    (Local.six-cell-window
      (Local.plain first) (Local.plain second) (Local.plain left)
      (Local.plain first') (Local.plain second') (Local.headed newQ newLeft))
    with BoolRec.all5
      (BoolRec.symbolEq machine first first')
      (BoolRec.symbolEq machine second second')
      (BoolRec.stateEq machine newQ q')
      (BoolRec.symbolEq machine newLeft left)
      (BoolRec.symbolEq machine left left)
... | false = rejected
... | true
    with all5True
      (BoolRec.symbolEq machine first first')
      (BoolRec.symbolEq machine second second')
      (BoolRec.stateEq machine newQ q')
      (BoolRec.symbolEq machine newLeft left)
      (BoolRec.symbolEq machine left left)
      refl
... | e1 , (e2 , (e3 , (e4 , e5)))
    with symbolEqTrue e1 | symbolEqTrue e2 | stateEqTrue e3
       | symbolEqTrue e4
... | refl | refl | refl | refl =
  accepted Pattern.left-overlap-minus-two

recognizeLegalWindow machine
    (Local.tape-rule q a q' b Local.moveLeft)
    (Local.six-cell-window
      (Local.plain context) (Local.plain left) (Local.headed oldQ oldA)
      (Local.plain context') (Local.headed newQ newLeft) (Local.plain newB))
    with BoolRec.all6
      (BoolRec.symbolEq machine context context')
      (BoolRec.stateEq machine oldQ q)
      (BoolRec.symbolEq machine oldA a)
      (BoolRec.stateEq machine newQ q')
      (BoolRec.symbolEq machine newLeft left)
      (BoolRec.symbolEq machine newB b)
... | false = rejected
... | true
    with all6True
      (BoolRec.symbolEq machine context context')
      (BoolRec.stateEq machine oldQ q)
      (BoolRec.symbolEq machine oldA a)
      (BoolRec.stateEq machine newQ q')
      (BoolRec.symbolEq machine newLeft left)
      (BoolRec.symbolEq machine newB b)
      refl
... | e1 , (e2 , (e3 , (e4 , (e5 , e6))))
    with symbolEqTrue e1 | stateEqTrue e2 | symbolEqTrue e3
       | stateEqTrue e4 | symbolEqTrue e5 | symbolEqTrue e6
... | refl | refl | refl | refl | refl | refl =
  accepted Pattern.left-overlap-minus-one

recognizeLegalWindow machine
    (Local.tape-rule q a q' b Local.moveLeft)
    (Local.six-cell-window
      (Local.headed oldQ oldA) (Local.plain right) (Local.plain context)
      (Local.plain newB) (Local.plain right') (Local.plain context'))
    with BoolRec.all6
      (BoolRec.stateEq machine oldQ q)
      (BoolRec.symbolEq machine oldA a)
      (BoolRec.symbolEq machine newB b)
      (BoolRec.symbolEq machine right right')
      (BoolRec.symbolEq machine context context')
      (BoolRec.symbolEq machine right right)
... | false = rejected
... | true
    with all6True
      (BoolRec.stateEq machine oldQ q)
      (BoolRec.symbolEq machine oldA a)
      (BoolRec.symbolEq machine newB b)
      (BoolRec.symbolEq machine right right')
      (BoolRec.symbolEq machine context context')
      (BoolRec.symbolEq machine right right)
      refl
... | e1 , (e2 , (e3 , (e4 , (e5 , e6))))
    with stateEqTrue e1 | symbolEqTrue e2 | symbolEqTrue e3
       | symbolEqTrue e4 | symbolEqTrue e5
... | refl | refl | refl | refl | refl =
  accepted Pattern.left-overlap-plus-one

recognizeLegalWindow machine
    (Local.tape-rule q a q' b Local.stayPut)
    (Local.six-cell-window
      (Local.plain context) (Local.plain left) (Local.headed oldQ oldA)
      (Local.plain context') (Local.plain left') (Local.headed newQ newB))
    with BoolRec.all6
      (BoolRec.symbolEq machine context context')
      (BoolRec.symbolEq machine left left')
      (BoolRec.stateEq machine oldQ q)
      (BoolRec.symbolEq machine oldA a)
      (BoolRec.stateEq machine newQ q')
      (BoolRec.symbolEq machine newB b)
... | false = rejected
... | true
    with all6True
      (BoolRec.symbolEq machine context context')
      (BoolRec.symbolEq machine left left')
      (BoolRec.stateEq machine oldQ q)
      (BoolRec.symbolEq machine oldA a)
      (BoolRec.stateEq machine newQ q')
      (BoolRec.symbolEq machine newB b)
      refl
... | e1 , (e2 , (e3 , (e4 , (e5 , e6))))
    with symbolEqTrue e1 | symbolEqTrue e2 | stateEqTrue e3
       | symbolEqTrue e4 | stateEqTrue e5 | symbolEqTrue e6
... | refl | refl | refl | refl | refl | refl =
  accepted Pattern.stay-overlap-minus-one

recognizeLegalWindow machine
    (Local.tape-rule q a q' b Local.stayPut)
    (Local.six-cell-window
      (Local.headed oldQ oldA) (Local.plain right) (Local.plain context)
      (Local.headed newQ newB) (Local.plain right') (Local.plain context'))
    with BoolRec.all6
      (BoolRec.stateEq machine oldQ q)
      (BoolRec.symbolEq machine oldA a)
      (BoolRec.stateEq machine newQ q')
      (BoolRec.symbolEq machine newB b)
      (BoolRec.symbolEq machine right right')
      (BoolRec.symbolEq machine context context')
... | false = rejected
... | true
    with all6True
      (BoolRec.stateEq machine oldQ q)
      (BoolRec.symbolEq machine oldA a)
      (BoolRec.stateEq machine newQ q')
      (BoolRec.symbolEq machine newB b)
      (BoolRec.symbolEq machine right right')
      (BoolRec.symbolEq machine context context')
      refl
... | e1 , (e2 , (e3 , (e4 , (e5 , e6))))
    with stateEqTrue e1 | symbolEqTrue e2 | stateEqTrue e3
       | symbolEqTrue e4 | symbolEqTrue e5 | symbolEqTrue e6
... | refl | refl | refl | refl | refl | refl =
  accepted Pattern.stay-overlap-plus-one

recognizeLegalWindow machine
    (Local.tape-rule q a q' b Local.moveRight)
    (Local.six-cell-window
      (Local.plain context) (Local.plain left) (Local.headed oldQ oldA)
      (Local.plain context') (Local.plain left') (Local.plain newB))
    with BoolRec.all6
      (BoolRec.symbolEq machine context context')
      (BoolRec.symbolEq machine left left')
      (BoolRec.stateEq machine oldQ q)
      (BoolRec.symbolEq machine oldA a)
      (BoolRec.symbolEq machine newB b)
      (BoolRec.symbolEq machine left left)
... | false = rejected
... | true
    with all6True
      (BoolRec.symbolEq machine context context')
      (BoolRec.symbolEq machine left left')
      (BoolRec.stateEq machine oldQ q)
      (BoolRec.symbolEq machine oldA a)
      (BoolRec.symbolEq machine newB b)
      (BoolRec.symbolEq machine left left)
      refl
... | e1 , (e2 , (e3 , (e4 , (e5 , e6))))
    with symbolEqTrue e1 | symbolEqTrue e2 | stateEqTrue e3
       | symbolEqTrue e4 | symbolEqTrue e5
... | refl | refl | refl | refl | refl =
  accepted Pattern.right-overlap-minus-one

recognizeLegalWindow machine
    (Local.tape-rule q a q' b Local.moveRight)
    (Local.six-cell-window
      (Local.headed oldQ oldA) (Local.plain right) (Local.plain context)
      (Local.plain newB) (Local.headed newQ newRight) (Local.plain context'))
    with BoolRec.all6
      (BoolRec.stateEq machine oldQ q)
      (BoolRec.symbolEq machine oldA a)
      (BoolRec.symbolEq machine newB b)
      (BoolRec.stateEq machine newQ q')
      (BoolRec.symbolEq machine newRight right)
      (BoolRec.symbolEq machine context context')
... | false = rejected
... | true
    with all6True
      (BoolRec.stateEq machine oldQ q)
      (BoolRec.symbolEq machine oldA a)
      (BoolRec.symbolEq machine newB b)
      (BoolRec.stateEq machine newQ q')
      (BoolRec.symbolEq machine newRight right)
      (BoolRec.symbolEq machine context context')
      refl
... | e1 , (e2 , (e3 , (e4 , (e5 , e6))))
    with stateEqTrue e1 | symbolEqTrue e2 | symbolEqTrue e3
       | stateEqTrue e4 | symbolEqTrue e5 | symbolEqTrue e6
... | refl | refl | refl | refl | refl | refl =
  accepted Pattern.right-overlap-plus-one

recognizeLegalWindow machine
    (Local.tape-rule q a q' b Local.moveRight)
    (Local.six-cell-window
      (Local.plain right) (Local.plain first) (Local.plain second)
      (Local.headed newQ newRight) (Local.plain first') (Local.plain second'))
    with BoolRec.all5
      (BoolRec.stateEq machine newQ q')
      (BoolRec.symbolEq machine newRight right)
      (BoolRec.symbolEq machine first first')
      (BoolRec.symbolEq machine second second')
      (BoolRec.symbolEq machine right right)
... | false = rejected
... | true
    with all5True
      (BoolRec.stateEq machine newQ q')
      (BoolRec.symbolEq machine newRight right)
      (BoolRec.symbolEq machine first first')
      (BoolRec.symbolEq machine second second')
      (BoolRec.symbolEq machine right right)
      refl
... | e1 , (e2 , (e3 , (e4 , e5)))
    with stateEqTrue e1 | symbolEqTrue e2
       | symbolEqTrue e3 | symbolEqTrue e4
... | refl | refl | refl | refl =
  accepted Pattern.right-overlap-plus-two

recognizeLegalWindow machine rule window =
  rejected

reflectedLegalWindowBool :
  (machine : Local.ConcreteTapeMachine) →
  (rule : Local.TapeRule
    (Local.State machine)
    (Local.Symbol machine)) →
  (window : Local.SixCellWindow machine) →
  Bool
reflectedLegalWindowBool machine rule window =
  recognitionBool (recognizeLegalWindow machine rule window)

recognitionAcceptedGivesSemantic :
  ∀ {machine rule window}
    (recognition : LegalWindowRecognition machine rule window) →
  recognitionBool recognition ≡ true →
  Pattern.LegalWindowForRule machine rule window
recognitionAcceptedGivesSemantic rejected ()
recognitionAcceptedGivesSemantic (accepted legal) refl =
  legal

booleanTrueImpliesSemanticLegal :
  ∀ {machine rule window} →
  reflectedLegalWindowBool machine rule window ≡ true →
  Pattern.LegalWindowForRule machine rule window
booleanTrueImpliesSemanticLegal {machine} {rule} {window} =
  recognitionAcceptedGivesSemantic
    (recognizeLegalWindow machine rule window)

semanticLegalImpliesReflectedBooleanTrue :
  ∀ {machine rule window} →
  Pattern.LegalWindowForRule machine rule window →
  reflectedLegalWindowBool machine rule window ≡ true
semanticLegalImpliesReflectedBooleanTrue
    {machine} Pattern.legal-unchanged
    rewrite Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _ =
  refl
semanticLegalImpliesReflectedBooleanTrue
    {machine} (Pattern.legal-centered Local.realizes-left)
    rewrite Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _ =
  refl
semanticLegalImpliesReflectedBooleanTrue
    {machine} (Pattern.legal-centered Local.realizes-stay)
    rewrite Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _ =
  refl
semanticLegalImpliesReflectedBooleanTrue
    {machine} (Pattern.legal-centered Local.realizes-right)
    rewrite Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _ =
  refl
semanticLegalImpliesReflectedBooleanTrue
    {machine} Pattern.left-overlap-minus-two
    rewrite Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _ =
  refl
semanticLegalImpliesReflectedBooleanTrue
    {machine} Pattern.left-overlap-minus-one
    rewrite Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _ =
  refl
semanticLegalImpliesReflectedBooleanTrue
    {machine} Pattern.left-overlap-plus-one
    rewrite Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _ =
  refl
semanticLegalImpliesReflectedBooleanTrue
    {machine} Pattern.stay-overlap-minus-one
    rewrite Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _ =
  refl
semanticLegalImpliesReflectedBooleanTrue
    {machine} Pattern.stay-overlap-plus-one
    rewrite Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _ =
  refl
semanticLegalImpliesReflectedBooleanTrue
    {machine} Pattern.right-overlap-minus-one
    rewrite Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _ =
  refl
semanticLegalImpliesReflectedBooleanTrue
    {machine} Pattern.right-overlap-plus-one
    rewrite Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _ =
  refl
semanticLegalImpliesReflectedBooleanTrue
    {machine} Pattern.right-overlap-plus-two
    rewrite Local.decideEqualRefl (Local.finiteState machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _
          | Local.decideEqualRefl (Local.finiteSymbol machine) _ =
  refl

record LegalWindowBooleanReflection
    (machine : Local.ConcreteTapeMachine)
    (rule : Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine))
    (window : Local.SixCellWindow machine) : Set where
  field
    booleanToSemantic :
      reflectedLegalWindowBool machine rule window ≡ true →
      Pattern.LegalWindowForRule machine rule window

    semanticToBoolean :
      Pattern.LegalWindowForRule machine rule window →
      reflectedLegalWindowBool machine rule window ≡ true

canonicalLegalWindowBooleanReflection :
  ∀ machine rule window →
  LegalWindowBooleanReflection machine rule window
canonicalLegalWindowBooleanReflection machine rule window = record
  { booleanToSemantic =
      booleanTrueImpliesSemanticLegal
  ; semanticToBoolean =
      semanticLegalImpliesReflectedBooleanTrue
  }

record ConcreteTapeLegalWindowReflectionBoundary : Set where
  constructor concrete-tape-legal-window-reflection-boundary
  field
    proofCarryingRecognizerPaid : Bool
    booleanToSemanticReflectionPaid : Bool
    semanticToBooleanReflectionPaid : Bool
    fullLegalWindowBooleanIffPaid : Bool
    canonicalSATWeldPaid : Bool
    runToSATPaid : Bool
    satToRunPaid : Bool
    genericCookLevinPaid : Bool
    pVsNPResolved : Bool

canonicalConcreteTapeLegalWindowReflectionBoundary :
  ConcreteTapeLegalWindowReflectionBoundary
canonicalConcreteTapeLegalWindowReflectionBoundary =
  concrete-tape-legal-window-reflection-boundary
    true true true true false false false false false
