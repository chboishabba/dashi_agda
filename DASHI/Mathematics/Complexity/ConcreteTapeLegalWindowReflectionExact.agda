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


checkUnchanged :
  ∀ {machine rule a b c a' b' c'} →
  a ≡ a' → b ≡ b' → c ≡ c' →
  Pattern.LegalWindowForRule machine rule
    (Local.six-cell-window
      (Local.plain a) (Local.plain b) (Local.plain c)
      (Local.plain a') (Local.plain b') (Local.plain c'))
checkUnchanged refl refl refl = Pattern.legal-unchanged

checkRealizesLeft :
  ∀ {machine q a q' b left right oldQ oldA newQ newLeft newB newRight} →
  oldQ ≡ q → oldA ≡ a → newQ ≡ q' → newLeft ≡ left → newB ≡ b → newRight ≡ right →
  Pattern.LegalWindowForRule machine
    (Local.tape-rule q a q' b Local.moveLeft)
    (Local.six-cell-window
      (Local.plain left) (Local.headed oldQ oldA) (Local.plain right)
      (Local.headed newQ newLeft) (Local.plain newB) (Local.plain newRight))
checkRealizesLeft refl refl refl refl refl refl =
  Pattern.legal-centered Local.realizes-left

checkRealizesStay :
  ∀ {machine q a q' b left right left' right' oldQ oldA newQ newB} →
  left ≡ left' → oldQ ≡ q → oldA ≡ a → newQ ≡ q' → newB ≡ b → right ≡ right' →
  Pattern.LegalWindowForRule machine
    (Local.tape-rule q a q' b Local.stayPut)
    (Local.six-cell-window
      (Local.plain left) (Local.headed oldQ oldA) (Local.plain right)
      (Local.plain left') (Local.headed newQ newB) (Local.plain right'))
checkRealizesStay refl refl refl refl refl refl =
  Pattern.legal-centered Local.realizes-stay

checkRealizesRight :
  ∀ {machine q a q' b left right left' oldQ oldA newQ newRight newB} →
  left ≡ left' → oldQ ≡ q → oldA ≡ a → newB ≡ b → newQ ≡ q' → newRight ≡ right →
  Pattern.LegalWindowForRule machine
    (Local.tape-rule q a q' b Local.moveRight)
    (Local.six-cell-window
      (Local.plain left) (Local.headed oldQ oldA) (Local.plain right)
      (Local.plain left') (Local.plain newB) (Local.headed newQ newRight))
checkRealizesRight refl refl refl refl refl refl =
  Pattern.legal-centered Local.realizes-right

checkLeftOverlapMinusTwo :
  ∀ {machine q a q' b first second left first' second' newQ newLeft} →
  first ≡ first' → second ≡ second' → newQ ≡ q' → newLeft ≡ left →
  Pattern.LegalWindowForRule machine
    (Local.tape-rule q a q' b Local.moveLeft)
    (Local.six-cell-window
      (Local.plain first) (Local.plain second) (Local.plain left)
      (Local.plain first') (Local.plain second') (Local.headed newQ newLeft))
checkLeftOverlapMinusTwo refl refl refl refl =
  Pattern.left-overlap-minus-two

checkLeftOverlapMinusOne :
  ∀ {machine q a q' b context left oldQ oldA context' newQ newLeft newB} →
  context ≡ context' → oldQ ≡ q → oldA ≡ a → newQ ≡ q' → newLeft ≡ left → newB ≡ b →
  Pattern.LegalWindowForRule machine
    (Local.tape-rule q a q' b Local.moveLeft)
    (Local.six-cell-window
      (Local.plain context) (Local.plain left) (Local.headed oldQ oldA)
      (Local.plain context') (Local.headed newQ newLeft) (Local.plain newB))
checkLeftOverlapMinusOne refl refl refl refl refl refl =
  Pattern.left-overlap-minus-one

checkLeftOverlapPlusOne :
  ∀ {machine q a q' b right context right' context' oldQ oldA newB} →
  oldQ ≡ q → oldA ≡ a → newB ≡ b → right ≡ right' → context ≡ context' →
  Pattern.LegalWindowForRule machine
    (Local.tape-rule q a q' b Local.moveLeft)
    (Local.six-cell-window
      (Local.headed oldQ oldA) (Local.plain right) (Local.plain context)
      (Local.plain newB) (Local.plain right') (Local.plain context'))
checkLeftOverlapPlusOne refl refl refl refl refl =
  Pattern.left-overlap-plus-one

checkStayOverlapMinusOne :
  ∀ {machine q a q' b context left context' left' oldQ oldA newQ newB} →
  context ≡ context' → left ≡ left' → oldQ ≡ q → oldA ≡ a → newQ ≡ q' → newB ≡ b →
  Pattern.LegalWindowForRule machine
    (Local.tape-rule q a q' b Local.stayPut)
    (Local.six-cell-window
      (Local.plain context) (Local.plain left) (Local.headed oldQ oldA)
      (Local.plain context') (Local.plain left') (Local.headed newQ newB))
checkStayOverlapMinusOne refl refl refl refl refl refl =
  Pattern.stay-overlap-minus-one

checkStayOverlapPlusOne :
  ∀ {machine q a q' b right context right' context' oldQ oldA newQ newB} →
  oldQ ≡ q → oldA ≡ a → newQ ≡ q' → newB ≡ b → right ≡ right' → context ≡ context' →
  Pattern.LegalWindowForRule machine
    (Local.tape-rule q a q' b Local.stayPut)
    (Local.six-cell-window
      (Local.headed oldQ oldA) (Local.plain right) (Local.plain context)
      (Local.headed newQ newB) (Local.plain right') (Local.plain context'))
checkStayOverlapPlusOne refl refl refl refl refl refl =
  Pattern.stay-overlap-plus-one

checkRightOverlapMinusOne :
  ∀ {machine q a q' b context left context' left' oldQ oldA newB} →
  context ≡ context' → left ≡ left' → oldQ ≡ q → oldA ≡ a → newB ≡ b →
  Pattern.LegalWindowForRule machine
    (Local.tape-rule q a q' b Local.moveRight)
    (Local.six-cell-window
      (Local.plain context) (Local.plain left) (Local.headed oldQ oldA)
      (Local.plain context') (Local.plain left') (Local.plain newB))
checkRightOverlapMinusOne refl refl refl refl refl =
  Pattern.right-overlap-minus-one

checkRightOverlapPlusOne :
  ∀ {machine q a q' b right context context' oldQ oldA newB newQ newRight} →
  oldQ ≡ q → oldA ≡ a → newB ≡ b → newQ ≡ q' → newRight ≡ right → context ≡ context' →
  Pattern.LegalWindowForRule machine
    (Local.tape-rule q a q' b Local.moveRight)
    (Local.six-cell-window
      (Local.headed oldQ oldA) (Local.plain right) (Local.plain context)
      (Local.plain newB) (Local.headed newQ newRight) (Local.plain context'))
checkRightOverlapPlusOne refl refl refl refl refl refl =
  Pattern.right-overlap-plus-one

checkRightOverlapPlusTwo :
  ∀ {machine q a q' b right first second first' second' newQ newRight} →
  newQ ≡ q' → newRight ≡ right → first ≡ first' → second ≡ second' →
  Pattern.LegalWindowForRule machine
    (Local.tape-rule q a q' b Local.moveRight)
    (Local.six-cell-window
      (Local.plain right) (Local.plain first) (Local.plain second)
      (Local.headed newQ newRight) (Local.plain first') (Local.plain second'))
checkRightOverlapPlusTwo refl refl refl refl =
  Pattern.right-overlap-plus-two

reflectedLegalWindowBool :
  (machine : Local.ConcreteTapeMachine) →
  (rule : Local.TapeRule
    (Local.State machine)
    (Local.Symbol machine)) →
  (window : Local.SixCellWindow machine) →
  Bool
reflectedLegalWindowBool = BoolRec.legalWindowBool

booleanTrueImpliesSemanticLegal :
  ∀ {machine rule window} →
  reflectedLegalWindowBool machine rule window ≡ true →
  Pattern.LegalWindowForRule machine rule window
booleanTrueImpliesSemanticLegal {machine} {rule}
    {Local.six-cell-window
      (Local.plain a) (Local.plain b) (Local.plain c)
      (Local.plain a') (Local.plain b') (Local.plain c')} eq
    with all3True
      (BoolRec.symbolEq machine a a')
      (BoolRec.symbolEq machine b b')
      (BoolRec.symbolEq machine c c')
      eq
... | ea , (eb , ec) =
  checkUnchanged (symbolEqTrue {machine} ea) (symbolEqTrue {machine} eb) (symbolEqTrue {machine} ec)

booleanTrueImpliesSemanticLegal {machine}
    {Local.tape-rule q a q' b Local.moveLeft}
    {Local.six-cell-window
      (Local.plain left) (Local.headed oldQ oldA) (Local.plain right)
      (Local.headed newQ newLeft) (Local.plain newB) (Local.plain newRight)} eq
    with all6True
      (BoolRec.stateEq machine oldQ q)
      (BoolRec.symbolEq machine oldA a)
      (BoolRec.stateEq machine newQ q')
      (BoolRec.symbolEq machine newLeft left)
      (BoolRec.symbolEq machine newB b)
      (BoolRec.symbolEq machine newRight right)
      eq
... | e1 , (e2 , (e3 , (e4 , (e5 , e6)))) =
  checkRealizesLeft (stateEqTrue {machine} e1) (symbolEqTrue {machine} e2) (stateEqTrue {machine} e3)
                    (symbolEqTrue {machine} e4) (symbolEqTrue {machine} e5) (symbolEqTrue {machine} e6)

booleanTrueImpliesSemanticLegal {machine}
    {Local.tape-rule q a q' b Local.moveLeft}
    {Local.six-cell-window
      (Local.plain first) (Local.plain second) (Local.plain left)
      (Local.plain first') (Local.plain second') (Local.headed newQ newLeft)} eq
    with all5True
      (BoolRec.symbolEq machine first first')
      (BoolRec.symbolEq machine second second')
      (BoolRec.stateEq machine newQ q')
      (BoolRec.symbolEq machine newLeft left)
      (BoolRec.symbolEq machine left left)
      eq
... | e1 , (e2 , (e3 , (e4 , e5))) =
  checkLeftOverlapMinusTwo (symbolEqTrue {machine} e1) (symbolEqTrue {machine} e2) (stateEqTrue {machine} e3)
                           (symbolEqTrue {machine} e4)

booleanTrueImpliesSemanticLegal {machine}
    {Local.tape-rule q a q' b Local.moveLeft}
    {Local.six-cell-window
      (Local.plain context) (Local.plain left) (Local.headed oldQ oldA)
      (Local.plain context') (Local.headed newQ newLeft) (Local.plain newB)} eq
    with all6True
      (BoolRec.symbolEq machine context context')
      (BoolRec.stateEq machine oldQ q)
      (BoolRec.symbolEq machine oldA a)
      (BoolRec.stateEq machine newQ q')
      (BoolRec.symbolEq machine newLeft left)
      (BoolRec.symbolEq machine newB b)
      eq
... | e1 , (e2 , (e3 , (e4 , (e5 , e6)))) =
  checkLeftOverlapMinusOne (symbolEqTrue {machine} e1) (stateEqTrue {machine} e2) (symbolEqTrue {machine} e3)
                           (stateEqTrue {machine} e4) (symbolEqTrue {machine} e5) (symbolEqTrue {machine} e6)

booleanTrueImpliesSemanticLegal {machine}
    {Local.tape-rule q a q' b Local.moveLeft}
    {Local.six-cell-window
      (Local.headed oldQ oldA) (Local.plain right) (Local.plain context)
      (Local.plain newB) (Local.plain right') (Local.plain context')} eq
    with all6True
      (BoolRec.stateEq machine oldQ q)
      (BoolRec.symbolEq machine oldA a)
      (BoolRec.symbolEq machine newB b)
      (BoolRec.symbolEq machine right right')
      (BoolRec.symbolEq machine context context')
      (BoolRec.symbolEq machine right right)
      eq
... | e1 , (e2 , (e3 , (e4 , (e5 , e6)))) =
  checkLeftOverlapPlusOne (stateEqTrue {machine} e1) (symbolEqTrue {machine} e2) (symbolEqTrue {machine} e3)
                          (symbolEqTrue {machine} e4) (symbolEqTrue {machine} e5)

booleanTrueImpliesSemanticLegal {machine}
    {Local.tape-rule q a q' b Local.stayPut}
    {Local.six-cell-window
      (Local.plain left) (Local.headed oldQ oldA) (Local.plain right)
      (Local.plain left') (Local.headed newQ newB) (Local.plain right')} eq
    with all6True
      (BoolRec.symbolEq machine left left')
      (BoolRec.stateEq machine oldQ q)
      (BoolRec.symbolEq machine oldA a)
      (BoolRec.stateEq machine newQ q')
      (BoolRec.symbolEq machine newB b)
      (BoolRec.symbolEq machine right right')
      eq
... | e1 , (e2 , (e3 , (e4 , (e5 , e6)))) =
  checkRealizesStay (symbolEqTrue {machine} e1) (stateEqTrue {machine} e2) (symbolEqTrue {machine} e3)
                    (stateEqTrue {machine} e4) (symbolEqTrue {machine} e5) (symbolEqTrue {machine} e6)

booleanTrueImpliesSemanticLegal {machine}
    {Local.tape-rule q a q' b Local.stayPut}
    {Local.six-cell-window
      (Local.plain context) (Local.plain left) (Local.headed oldQ oldA)
      (Local.plain context') (Local.plain left') (Local.headed newQ newB)} eq
    with all6True
      (BoolRec.symbolEq machine context context')
      (BoolRec.symbolEq machine left left')
      (BoolRec.stateEq machine oldQ q)
      (BoolRec.symbolEq machine oldA a)
      (BoolRec.stateEq machine newQ q')
      (BoolRec.symbolEq machine newB b)
      eq
... | e1 , (e2 , (e3 , (e4 , (e5 , e6)))) =
  checkStayOverlapMinusOne (symbolEqTrue {machine} e1) (symbolEqTrue {machine} e2) (stateEqTrue {machine} e3)
                           (symbolEqTrue {machine} e4) (stateEqTrue {machine} e5) (symbolEqTrue {machine} e6)

booleanTrueImpliesSemanticLegal {machine}
    {Local.tape-rule q a q' b Local.stayPut}
    {Local.six-cell-window
      (Local.headed oldQ oldA) (Local.plain right) (Local.plain context)
      (Local.headed newQ newB) (Local.plain right') (Local.plain context')} eq
    with all6True
      (BoolRec.stateEq machine oldQ q)
      (BoolRec.symbolEq machine oldA a)
      (BoolRec.stateEq machine newQ q')
      (BoolRec.symbolEq machine newB b)
      (BoolRec.symbolEq machine right right')
      (BoolRec.symbolEq machine context context')
      eq
... | e1 , (e2 , (e3 , (e4 , (e5 , e6)))) =
  checkStayOverlapPlusOne (stateEqTrue {machine} e1) (symbolEqTrue {machine} e2) (stateEqTrue {machine} e3)
                          (symbolEqTrue {machine} e4) (symbolEqTrue {machine} e5) (symbolEqTrue {machine} e6)

booleanTrueImpliesSemanticLegal {machine}
    {Local.tape-rule q a q' b Local.moveRight}
    {Local.six-cell-window
      (Local.plain left) (Local.headed oldQ oldA) (Local.plain right)
      (Local.plain left') (Local.plain newB) (Local.headed newQ newRight)} eq
    with all6True
      (BoolRec.symbolEq machine left left')
      (BoolRec.stateEq machine oldQ q)
      (BoolRec.symbolEq machine oldA a)
      (BoolRec.symbolEq machine newB b)
      (BoolRec.stateEq machine newQ q')
      (BoolRec.symbolEq machine newRight right)
      eq
... | e1 , (e2 , (e3 , (e4 , (e5 , e6)))) =
  checkRealizesRight (symbolEqTrue {machine} e1) (stateEqTrue {machine} e2) (symbolEqTrue {machine} e3)
                     (symbolEqTrue {machine} e4) (stateEqTrue {machine} e5) (symbolEqTrue {machine} e6)

booleanTrueImpliesSemanticLegal {machine}
    {Local.tape-rule q a q' b Local.moveRight}
    {Local.six-cell-window
      (Local.plain context) (Local.plain left) (Local.headed oldQ oldA)
      (Local.plain context') (Local.plain left') (Local.plain newB)} eq
    with all6True
      (BoolRec.symbolEq machine context context')
      (BoolRec.symbolEq machine left left')
      (BoolRec.stateEq machine oldQ q)
      (BoolRec.symbolEq machine oldA a)
      (BoolRec.symbolEq machine newB b)
      (BoolRec.symbolEq machine left left)
      eq
... | e1 , (e2 , (e3 , (e4 , (e5 , e6)))) =
  checkRightOverlapMinusOne (symbolEqTrue {machine} e1) (symbolEqTrue {machine} e2) (stateEqTrue {machine} e3)
                            (symbolEqTrue {machine} e4) (symbolEqTrue {machine} e5)

booleanTrueImpliesSemanticLegal {machine}
    {Local.tape-rule q a q' b Local.moveRight}
    {Local.six-cell-window
      (Local.headed oldQ oldA) (Local.plain right) (Local.plain context)
      (Local.plain newB) (Local.headed newQ newRight) (Local.plain context')} eq
    with all6True
      (BoolRec.stateEq machine oldQ q)
      (BoolRec.symbolEq machine oldA a)
      (BoolRec.symbolEq machine newB b)
      (BoolRec.stateEq machine newQ q')
      (BoolRec.symbolEq machine newRight right)
      (BoolRec.symbolEq machine context context')
      eq
... | e1 , (e2 , (e3 , (e4 , (e5 , e6)))) =
  checkRightOverlapPlusOne (stateEqTrue {machine} e1) (symbolEqTrue {machine} e2) (symbolEqTrue {machine} e3)
                           (stateEqTrue {machine} e4) (symbolEqTrue {machine} e5) (symbolEqTrue {machine} e6)

booleanTrueImpliesSemanticLegal {machine}
    {Local.tape-rule q a q' b Local.moveRight}
    {Local.six-cell-window
      (Local.plain right) (Local.plain first) (Local.plain second)
      (Local.headed newQ newRight) (Local.plain first') (Local.plain second')} eq
    with all5True
      (BoolRec.stateEq machine newQ q')
      (BoolRec.symbolEq machine newRight right)
      (BoolRec.symbolEq machine first first')
      (BoolRec.symbolEq machine second second')
      (BoolRec.symbolEq machine right right)
      eq
... | e1 , (e2 , (e3 , (e4 , e5))) =
  checkRightOverlapPlusTwo (stateEqTrue {machine} e1) (symbolEqTrue {machine} e2)
                           (symbolEqTrue {machine} e3) (symbolEqTrue {machine} e4)

booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveLeft} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.stayPut} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _) (Local.headed _ _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.plain _)} ()
booleanTrueImpliesSemanticLegal {machine} {Local.tape-rule _ _ _ _ Local.moveRight} {Local.six-cell-window (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _) (Local.headed _ _)} ()

semanticLegalImpliesReflectedBooleanTrue :
  ∀ {machine rule window} →
  Pattern.LegalWindowForRule machine rule window →
  reflectedLegalWindowBool machine rule window ≡ true
semanticLegalImpliesReflectedBooleanTrue =
  BoolRec.semanticLegalImpliesBooleanTrue

recognizeLegalWindow :
  (machine : Local.ConcreteTapeMachine) →
  (rule : Local.TapeRule
    (Local.State machine)
    (Local.Symbol machine)) →
  (window : Local.SixCellWindow machine) →
  LegalWindowRecognition machine rule window
recognizeLegalWindow machine rule window
  with reflectedLegalWindowBool machine rule window in eq
... | false = rejected
... | true = accepted (booleanTrueImpliesSemanticLegal eq)

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
