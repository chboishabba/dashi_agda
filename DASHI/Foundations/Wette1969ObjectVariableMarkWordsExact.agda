module DASHI.Foundations.Wette1969ObjectVariableMarkWordsExact where

------------------------------------------------------------------------
-- WETTE 1969 OBJECT-LANGUAGE VARIABLE / PREDICATE-MARK WORDS
--
-- Eduard Wette,
-- "Definition eines (relativ vollständigen) formalen Systems konstruktiver
-- Arithmetik", Foundations of Mathematics, Springer 1969, pp. 130--195.
-- DOI: 10.1007/978-3-642-86745-3_9
--
-- Source loci:
--   * printed p.144, rules 3 and 4: variables and predicate marks are words
--     built from the variable kernel / predicate-mark kernel by the Juxtor;
--   * printed p.148: ξ is the Variablenkern, Π the Prädikatmarkenkern, and
--     juxtaposition is the binary functor u;
--   * p.148: xW means "W is a natural-number variable" and nVW means
--     "W is a mark for V-place predicates".
--
-- This is object-language syntax.  It is deliberately distinct from the nineteen
-- `WordVariable`s used metasyntactically in Wette's rule schemata.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature

WordTerm = Signature.WordTerm

juxtapose : WordTerm → WordTerm → WordTerm
juxtapose left right =
  Signature.binaryWordTerm Signature.juxtapositionFunctor refl left right

variableKernelWord : WordTerm
variableKernelWord = Signature.constantWordTerm Signature.variableKernel

predicateMarkKernelWord : WordTerm
predicateMarkKernelWord = Signature.constantWordTerm Signature.predicateMarkKernel

objectVariableWord : WordTerm → WordTerm
objectVariableWord index = juxtapose variableKernelWord index

predicateMarkWord : WordTerm → WordTerm → WordTerm
predicateMarkWord arity index =
  juxtapose (juxtapose predicateMarkKernelWord arity) index

data IsObjectVariableWord : WordTerm → Set where
  isObjectVariableWord :
    (index : WordTerm) →
    IsObjectVariableWord (objectVariableWord index)

data IsPredicateMarkWord : WordTerm → Set where
  isPredicateMarkWord :
    (arity index : WordTerm) →
    IsPredicateMarkWord (predicateMarkWord arity index)

record ObjectVariableView (word : WordTerm) : Set where
  constructor objectVariableView
  field
    index : WordTerm
    wordIsVariableConstruction : word ≡ objectVariableWord index

open ObjectVariableView public

record PredicateMarkView (word : WordTerm) : Set where
  constructor predicateMarkView
  field
    arity : WordTerm
    index : WordTerm
    wordIsPredicateMarkConstruction : word ≡ predicateMarkWord arity index

open PredicateMarkView public

canonicalObjectVariableView :
  (index : WordTerm) → ObjectVariableView (objectVariableWord index)
canonicalObjectVariableView index = objectVariableView index refl

canonicalPredicateMarkView :
  (arity index : WordTerm) → PredicateMarkView (predicateMarkWord arity index)
canonicalPredicateMarkView arity index = predicateMarkView arity index refl

objectVariableViewRecognizesObjectSyntax :
  ∀ {word} → ObjectVariableView word → IsObjectVariableWord word
objectVariableViewRecognizesObjectSyntax (objectVariableView index refl) =
  isObjectVariableWord index

predicateMarkViewRecognizesObjectSyntax :
  ∀ {word} → PredicateMarkView word → IsPredicateMarkWord word
predicateMarkViewRecognizesObjectSyntax (predicateMarkView arity index refl) =
  isPredicateMarkWord arity index

record Wette1969ObjectVariableMarkWordsBoundary : Set where
  constructor wette1969ObjectVariableMarkWordsBoundary
  field
    objectVariableConstructorRecoveredFromRule3 : Bool
    objectVariableConstructorRecoveredFromRule3IsTrue :
      objectVariableConstructorRecoveredFromRule3 ≡ true

    predicateMarkConstructorRecoveredFromRule4 : Bool
    predicateMarkConstructorRecoveredFromRule4IsTrue :
      predicateMarkConstructorRecoveredFromRule4 ≡ true

    objectSyntaxSeparatedFromRuleSchematicWordVariables : Bool
    objectSyntaxSeparatedFromRuleSchematicWordVariablesIsTrue :
      objectSyntaxSeparatedFromRuleSchematicWordVariables ≡ true

    proofRelevantObjectSyntaxRecognitionNowAvailable : Bool
    proofRelevantObjectSyntaxRecognitionNowAvailableIsTrue :
      proofRelevantObjectSyntaxRecognitionNowAvailable ≡ true

    constructorsAlreadyProveNaturalNumberIndexJudgements : Bool
    constructorsAlreadyProveNaturalNumberIndexJudgementsIsFalse :
      constructorsAlreadyProveNaturalNumberIndexJudgements ≡ false

    constructorsAlreadyDecideHistoricalWellFormedness : Bool
    constructorsAlreadyDecideHistoricalWellFormednessIsFalse :
      constructorsAlreadyDecideHistoricalWellFormedness ≡ false

canonicalWette1969ObjectVariableMarkWordsBoundary :
  Wette1969ObjectVariableMarkWordsBoundary
canonicalWette1969ObjectVariableMarkWordsBoundary =
  wette1969ObjectVariableMarkWordsBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
