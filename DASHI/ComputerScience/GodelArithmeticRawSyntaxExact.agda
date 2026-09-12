module DASHI.ComputerScience.GodelArithmeticRawSyntaxExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- CONCRETE RAW FIRST-ORDER ARITHMETIC SYNTAX
--
-- This fixes the recursive carrier that future Gödel coding is allowed to
-- encode.  Variables are de Bruijn indices.  The module deliberately stops
-- before capture-avoiding substitution/instantiation, proof theory, or any
-- representability theorem.
------------------------------------------------------------------------

data ArithmeticTerm : Set where
  variableTerm : Nat → ArithmeticTerm
  zeroTerm : ArithmeticTerm
  successorTerm : ArithmeticTerm → ArithmeticTerm
  addTerm : ArithmeticTerm → ArithmeticTerm → ArithmeticTerm
  multiplyTerm : ArithmeticTerm → ArithmeticTerm → ArithmeticTerm

data ArithmeticFormula : Set where
  equalFormula : ArithmeticTerm → ArithmeticTerm → ArithmeticFormula
  falseFormula : ArithmeticFormula
  implyFormula : ArithmeticFormula → ArithmeticFormula → ArithmeticFormula
  forallFormula : ArithmeticFormula → ArithmeticFormula

------------------------------------------------------------------------
-- Structural size.  This is useful for later bounded decoders/induction, but
-- it is NOT a Gödel code and is intentionally non-injective.
------------------------------------------------------------------------

termSize : ArithmeticTerm → Nat
termSize (variableTerm _) = 1
termSize zeroTerm = 1
termSize (successorTerm t) = 1 + termSize t
termSize (addTerm left right) = 1 + termSize left + termSize right
termSize (multiplyTerm left right) = 1 + termSize left + termSize right

formulaSize : ArithmeticFormula → Nat
formulaSize (equalFormula left right) = 1 + termSize left + termSize right
formulaSize falseFormula = 1
formulaSize (implyFormula left right) = 1 + formulaSize left + formulaSize right
formulaSize (forallFormula body) = 1 + formulaSize body

------------------------------------------------------------------------
-- Canonical tiny specimens.  These establish only the raw syntax surface.
------------------------------------------------------------------------

x0 : ArithmeticTerm
x0 = variableTerm 0

x1 : ArithmeticTerm
x1 = variableTerm 1

oneTerm : ArithmeticTerm
oneTerm = successorTerm zeroTerm

x0EqualsX0 : ArithmeticFormula
x0EqualsX0 = equalFormula x0 x0

forallX0EqualsX0 : ArithmeticFormula
forallX0EqualsX0 = forallFormula x0EqualsX0

------------------------------------------------------------------------
-- Exact boundaries.
------------------------------------------------------------------------

data StructuralSizeIsGodelCode : Set where
data RawSyntaxSuppliesCaptureAvoidingInstantiation : Set where
data RawSyntaxSuppliesFormulaNatRetraction : Set where
data RawSyntaxSuppliesProvability : Set where
data RawSyntaxSuppliesRepresentability : Set where

structuralSizeIsNotPromotedToGodelCode : StructuralSizeIsGodelCode → ⊥
structuralSizeIsNotPromotedToGodelCode ()

rawSyntaxDoesNotSupplyInstantiation :
  RawSyntaxSuppliesCaptureAvoidingInstantiation → ⊥
rawSyntaxDoesNotSupplyInstantiation ()

rawSyntaxDoesNotSupplyFormulaNatRetraction :
  RawSyntaxSuppliesFormulaNatRetraction → ⊥
rawSyntaxDoesNotSupplyFormulaNatRetraction ()

rawSyntaxDoesNotSupplyProvability : RawSyntaxSuppliesProvability → ⊥
rawSyntaxDoesNotSupplyProvability ()

rawSyntaxDoesNotSupplyRepresentability : RawSyntaxSuppliesRepresentability → ⊥
rawSyntaxDoesNotSupplyRepresentability ()

record GodelArithmeticRawSyntaxBoundary : Set where
  constructor godelArithmeticRawSyntaxBoundary
  field
    recursiveArithmeticTermCarrierOwned : Bool
    recursiveArithmeticFormulaCarrierOwned : Bool
    deBruijnVariableConventionOwned : Bool
    arithmeticZeroSuccessorAddMultiplyOwned : Bool
    equalityImplicationFalsityForallOwned : Bool
    structuralSizeOwned : Bool
    structuralSizePromotedToGodelCode : Bool
    captureAvoidingInstantiationOwned : Bool
    formulaNatRetractionOwned : Bool
    provabilityPredicateOwned : Bool
    selfSubstitutionRepresentabilityOwned : Bool

canonicalGodelArithmeticRawSyntaxBoundary : GodelArithmeticRawSyntaxBoundary
canonicalGodelArithmeticRawSyntaxBoundary =
  godelArithmeticRawSyntaxBoundary
    true true true true true true false false false false false
