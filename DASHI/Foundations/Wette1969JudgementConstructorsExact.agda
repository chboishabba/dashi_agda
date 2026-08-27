module DASHI.Foundations.Wette1969JudgementConstructorsExact where

------------------------------------------------------------------------
-- WETTE 1969 HISTORICAL JUDGEMENT CONSTRUCTORS
--
-- Eduard Wette,
-- "Definition eines (relativ vollständigen) formalen Systems konstruktiver
-- Arithmetik", Foundations of Mathematics, Springer 1969, pp. 130--195.
-- DOI: 10.1007/978-3-642-86745-3_9
--
-- Primary source locus: printed p.148, where Wette gives the intended reading
-- of the relators used by the pure calculus.  These constructors merely make
-- the corresponding arity-indexed Formula values convenient to build.  They do
-- not add semantic truth beyond the historical syntax.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to []ᵥ; _∷_ to _∷ᵥ_)

import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature

WordTerm = Signature.WordTerm
Formula = Signature.Formula

unaryJudgement : Signature.HistoricalRelator → WordTerm → Formula
unaryJudgement relator term =
  Signature.historicalFormula relator (term ∷ᵥ []ᵥ)

binaryJudgement :
  Signature.HistoricalRelator → WordTerm → WordTerm → Formula
binaryJudgement relator left right =
  Signature.historicalFormula relator (left ∷ᵥ right ∷ᵥ []ᵥ)

ternaryJudgement :
  Signature.HistoricalRelator →
  WordTerm → WordTerm → WordTerm → Formula
ternaryJudgement relator first second third =
  Signature.historicalFormula relator
    (first ∷ᵥ second ∷ᵥ third ∷ᵥ []ᵥ)

quaternaryJudgement :
  Signature.HistoricalRelator →
  WordTerm → WordTerm → WordTerm → WordTerm → Formula
quaternaryJudgement relator first second third fourth =
  Signature.historicalFormula relator
    (first ∷ᵥ second ∷ᵥ third ∷ᵥ fourth ∷ᵥ []ᵥ)

naturalNumber : WordTerm → Formula
naturalNumber = unaryJudgement Signature.naturalNumberRelator

naturalVariable : WordTerm → Formula
naturalVariable = unaryJudgement Signature.naturalVariableRelator

naturalTerm : WordTerm → Formula
naturalTerm = unaryJudgement Signature.naturalTermRelator

assertionSchema : WordTerm → Formula
assertionSchema = unaryJudgement Signature.assertionSchemaRelator

assertionSchemaNoPredicateQuantification : WordTerm → Formula
assertionSchemaNoPredicateQuantification =
  unaryJudgement Signature.assertionSchemaNoPredicateQuantificationRelator

unequal : WordTerm → WordTerm → Formula
unequal = binaryJudgement Signature.inequalityRelator

duplicates : WordTerm → WordTerm → Formula
duplicates = binaryJudgement Signature.duplicationRelator

predicateMarkArity : WordTerm → WordTerm → Formula
predicateMarkArity = binaryJudgement Signature.predicateMarkArityRelator

termTuple : WordTerm → WordTerm → Formula
termTuple = binaryJudgement Signature.termTupleRelator

freeForSyntax : WordTerm → WordTerm → Formula
freeForSyntax = binaryJudgement Signature.freeForSyntaxRelator

distinctVariableTuple : WordTerm → WordTerm → Formula
distinctVariableTuple = binaryJudgement Signature.distinctVariableTupleRelator

predicateSchema : WordTerm → WordTerm → Formula
predicateSchema = binaryJudgement Signature.predicateSchemaRelator

implies : WordTerm → WordTerm → Formula
implies = binaryJudgement Signature.implicationDerivabilityRelator

abbreviates : WordTerm → WordTerm → Formula
abbreviates = binaryJudgement Signature.abbreviationRelator

juxtapositionResult : WordTerm → WordTerm → WordTerm → Formula
juxtapositionResult = ternaryJudgement Signature.juxtapositionResultRelator

substitution :
  WordTerm → WordTerm → WordTerm → WordTerm → Formula
substitution = quaternaryJudgement Signature.substitutionRelator

------------------------------------------------------------------------
-- Regression facts: the constructor selected really is the expected relator.
------------------------------------------------------------------------

substitutionHasSubstitutionRelator :
  (a b c d : WordTerm) →
  Signature.relator (substitution a b c d) ≡ Signature.substitutionRelator
substitutionHasSubstitutionRelator a b c d = refl

freeForSyntaxHasFreshnessRelator :
  (a b : WordTerm) →
  Signature.relator (freeForSyntax a b) ≡ Signature.freeForSyntaxRelator
freeForSyntaxHasFreshnessRelator a b = refl

distinctVariableTupleHasExpectedRelator :
  (a b : WordTerm) →
  Signature.relator (distinctVariableTuple a b)
    ≡ Signature.distinctVariableTupleRelator
distinctVariableTupleHasExpectedRelator a b = refl

record Wette1969JudgementConstructorBoundary : Set where
  constructor wette1969JudgementConstructorBoundary
  field
    allHistoricalRelatorAritiesHaveTypedConstructors : Bool
    allHistoricalRelatorAritiesHaveTypedConstructorsIsTrue :
      allHistoricalRelatorAritiesHaveTypedConstructors ≡ true

    constructorLayerAddsSemanticTruth : Bool
    constructorLayerAddsSemanticTruthIsFalse :
      constructorLayerAddsSemanticTruth ≡ false

    typedConstructorAlreadyRecoversCriticalRuleArguments : Bool
    typedConstructorAlreadyRecoversCriticalRuleArgumentsIsFalse :
      typedConstructorAlreadyRecoversCriticalRuleArguments ≡ false

canonicalWette1969JudgementConstructorBoundary :
  Wette1969JudgementConstructorBoundary
canonicalWette1969JudgementConstructorBoundary =
  wette1969JudgementConstructorBoundary
    true refl
    false refl
    false refl
