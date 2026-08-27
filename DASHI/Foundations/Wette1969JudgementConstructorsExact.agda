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

naturalNumber : WordTerm → Formula
naturalNumber term =
  Signature.historicalFormula Signature.naturalNumberRelator
    (term ∷ᵥ []ᵥ)

naturalVariable : WordTerm → Formula
naturalVariable term =
  Signature.historicalFormula Signature.naturalVariableRelator
    (term ∷ᵥ []ᵥ)

naturalTerm : WordTerm → Formula
naturalTerm term =
  Signature.historicalFormula Signature.naturalTermRelator
    (term ∷ᵥ []ᵥ)

assertionSchema : WordTerm → Formula
assertionSchema term =
  Signature.historicalFormula Signature.assertionSchemaRelator
    (term ∷ᵥ []ᵥ)

assertionSchemaNoPredicateQuantification : WordTerm → Formula
assertionSchemaNoPredicateQuantification term =
  Signature.historicalFormula
    Signature.assertionSchemaNoPredicateQuantificationRelator
    (term ∷ᵥ []ᵥ)

unequal : WordTerm → WordTerm → Formula
unequal left right =
  Signature.historicalFormula Signature.inequalityRelator
    (left ∷ᵥ right ∷ᵥ []ᵥ)

duplicates : WordTerm → WordTerm → Formula
duplicates left right =
  Signature.historicalFormula Signature.duplicationRelator
    (left ∷ᵥ right ∷ᵥ []ᵥ)

predicateMarkArity : WordTerm → WordTerm → Formula
predicateMarkArity arity mark =
  Signature.historicalFormula Signature.predicateMarkArityRelator
    (arity ∷ᵥ mark ∷ᵥ []ᵥ)

termTuple : WordTerm → WordTerm → Formula
termTuple arity tuple =
  Signature.historicalFormula Signature.termTupleRelator
    (arity ∷ᵥ tuple ∷ᵥ []ᵥ)

freeForSyntax : WordTerm → WordTerm → Formula
freeForSyntax left right =
  Signature.historicalFormula Signature.freeForSyntaxRelator
    (left ∷ᵥ right ∷ᵥ []ᵥ)

distinctVariableTuple : WordTerm → WordTerm → Formula
distinctVariableTuple arity tuple =
  Signature.historicalFormula Signature.distinctVariableTupleRelator
    (arity ∷ᵥ tuple ∷ᵥ []ᵥ)

predicateSchema : WordTerm → WordTerm → Formula
predicateSchema arity schema =
  Signature.historicalFormula Signature.predicateSchemaRelator
    (arity ∷ᵥ schema ∷ᵥ []ᵥ)

implies : WordTerm → WordTerm → Formula
implies antecedent consequent =
  Signature.historicalFormula Signature.implicationDerivabilityRelator
    (antecedent ∷ᵥ consequent ∷ᵥ []ᵥ)

abbreviates : WordTerm → WordTerm → Formula
abbreviates abbreviation expanded =
  Signature.historicalFormula Signature.abbreviationRelator
    (abbreviation ∷ᵥ expanded ∷ᵥ []ᵥ)

juxtapositionResult : WordTerm → WordTerm → WordTerm → Formula
juxtapositionResult left right result =
  Signature.historicalFormula Signature.juxtapositionResultRelator
    (left ∷ᵥ right ∷ᵥ result ∷ᵥ []ᵥ)

substitution :
  WordTerm → WordTerm → WordTerm → WordTerm → Formula
substitution substitutedIn source replacement result =
  Signature.historicalFormula Signature.substitutionRelator
    (substitutedIn ∷ᵥ source ∷ᵥ replacement ∷ᵥ result ∷ᵥ []ᵥ)

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
