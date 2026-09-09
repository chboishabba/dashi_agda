module DASHI.ComputerScience.GodelArithmeticDeBruijnInstantiationExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.GodelArithmeticRawSyntaxExact as Syntax

------------------------------------------------------------------------
-- CAPTURE-AVOIDING TERM INSTANTIATION ON THE RAW ARITHMETIC CARRIER
--
-- Variables are de Bruijn indices.  Substituting for variable j under one
-- quantifier increments j and shifts every free variable in the replacement.
-- Arithmetic terms contain no binders, so that shift is structurally simple.
------------------------------------------------------------------------

natEqual : Nat → Nat → Bool
natEqual 0 0 = true
natEqual 0 (suc _) = false
natEqual (suc _) 0 = false
natEqual (suc left) (suc right) = natEqual left right

shiftTerm : Syntax.ArithmeticTerm → Syntax.ArithmeticTerm
shiftTerm (Syntax.variableTerm index) = Syntax.variableTerm (suc index)
shiftTerm Syntax.zeroTerm = Syntax.zeroTerm
shiftTerm (Syntax.successorTerm term) =
  Syntax.successorTerm (shiftTerm term)
shiftTerm (Syntax.addTerm left right) =
  Syntax.addTerm (shiftTerm left) (shiftTerm right)
shiftTerm (Syntax.multiplyTerm left right) =
  Syntax.multiplyTerm (shiftTerm left) (shiftTerm right)

substituteTerm :
  Nat →
  Syntax.ArithmeticTerm →
  Syntax.ArithmeticTerm →
  Syntax.ArithmeticTerm
substituteTerm variable replacement (Syntax.variableTerm index)
  with natEqual variable index
... | true = replacement
... | false = Syntax.variableTerm index
substituteTerm variable replacement Syntax.zeroTerm = Syntax.zeroTerm
substituteTerm variable replacement (Syntax.successorTerm term) =
  Syntax.successorTerm (substituteTerm variable replacement term)
substituteTerm variable replacement (Syntax.addTerm left right) =
  Syntax.addTerm
    (substituteTerm variable replacement left)
    (substituteTerm variable replacement right)
substituteTerm variable replacement (Syntax.multiplyTerm left right) =
  Syntax.multiplyTerm
    (substituteTerm variable replacement left)
    (substituteTerm variable replacement right)

substituteFormula :
  Nat →
  Syntax.ArithmeticTerm →
  Syntax.ArithmeticFormula →
  Syntax.ArithmeticFormula
substituteFormula variable replacement (Syntax.equalFormula left right) =
  Syntax.equalFormula
    (substituteTerm variable replacement left)
    (substituteTerm variable replacement right)
substituteFormula variable replacement Syntax.falseFormula =
  Syntax.falseFormula
substituteFormula variable replacement (Syntax.implyFormula left right) =
  Syntax.implyFormula
    (substituteFormula variable replacement left)
    (substituteFormula variable replacement right)
substituteFormula variable replacement (Syntax.forallFormula body) =
  Syntax.forallFormula
    (substituteFormula (suc variable) (shiftTerm replacement) body)

------------------------------------------------------------------------
-- Numerals and the distinguished-free-variable instantiation used by the
-- diagonal contract.  This does not assert that every raw formula has exactly
-- one free variable; it gives the operation on the chosen convention x_0.
------------------------------------------------------------------------

numeralTerm : Nat → Syntax.ArithmeticTerm
numeralTerm 0 = Syntax.zeroTerm
numeralTerm (suc n) = Syntax.successorTerm (numeralTerm n)

instantiateX0 :
  Syntax.ArithmeticFormula →
  Syntax.ArithmeticTerm →
  Syntax.ArithmeticFormula
instantiateX0 formula replacement =
  substituteFormula 0 replacement formula

------------------------------------------------------------------------
-- Exact small regressions.
------------------------------------------------------------------------

instantiateX0InReflexiveEquality :
  (term : Syntax.ArithmeticTerm) →
  instantiateX0 Syntax.x0EqualsX0 term
  ≡ Syntax.equalFormula term term
instantiateX0InReflexiveEquality term = refl

shiftNumeral :
  (n : Nat) →
  shiftTerm (numeralTerm n) ≡ numeralTerm n
shiftNumeral 0 = refl
shiftNumeral (suc n)
  rewrite shiftNumeral n = refl

boundVariableZeroIsProtected :
  (replacement : Syntax.ArithmeticTerm) →
  substituteFormula 0 replacement
    (Syntax.forallFormula
      (Syntax.equalFormula
        (Syntax.variableTerm 0)
        (Syntax.variableTerm 0)))
  ≡
  Syntax.forallFormula
    (Syntax.equalFormula
      (Syntax.variableTerm 0)
      (Syntax.variableTerm 0))
boundVariableZeroIsProtected replacement = refl

freeVariableAcrossBinderUsesShiftedReplacement :
  (replacement : Syntax.ArithmeticTerm) →
  substituteFormula 0 replacement
    (Syntax.forallFormula
      (Syntax.equalFormula
        (Syntax.variableTerm 1)
        (Syntax.variableTerm 1)))
  ≡
  Syntax.forallFormula
    (Syntax.equalFormula
      (shiftTerm replacement)
      (shiftTerm replacement))
freeVariableAcrossBinderUsesShiftedReplacement replacement = refl

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

data RawInstantiationIsArithmetisedSubstitution : Set where
data RawSubstitutionProvesRepresentability : Set where
data DistinguishedX0ConventionProvesUnaryWellFormedness : Set where

rawInstantiationIsNotYetCodeSubstitution :
  RawInstantiationIsArithmetisedSubstitution → ⊥
rawInstantiationIsNotYetCodeSubstitution ()

rawSubstitutionDoesNotProveRepresentability :
  RawSubstitutionProvesRepresentability → ⊥
rawSubstitutionDoesNotProveRepresentability ()

x0ConventionDoesNotProveUnaryWellFormedness :
  DistinguishedX0ConventionProvesUnaryWellFormedness → ⊥
x0ConventionDoesNotProveUnaryWellFormedness ()

record GodelArithmeticInstantiationBoundary : Set where
  constructor godelArithmeticInstantiationBoundary
  field
    deBruijnShiftOwned : Bool
    termSubstitutionOwned : Bool
    captureAvoidingFormulaSubstitutionOwned : Bool
    numeralConstructionOwned : Bool
    distinguishedX0InstantiationOwned : Bool
    formulaNatRetractionOwned : Bool
    arithmetisedCodeSubstitutionOwnedFromThisModule : Bool
    representabilityOwned : Bool

canonicalGodelArithmeticInstantiationBoundary :
  GodelArithmeticInstantiationBoundary
canonicalGodelArithmeticInstantiationBoundary =
  godelArithmeticInstantiationBoundary
    true true true true true false false false
