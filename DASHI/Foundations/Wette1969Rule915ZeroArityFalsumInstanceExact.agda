module DASHI.Foundations.Wette1969Rule915ZeroArityFalsumInstanceExact where

------------------------------------------------------------------------
-- ONE CONCRETE COHERENT 9.1.5 INSTANCE
--
-- Arity is zero, all variable tuples are empty, the condition/definition
-- prerequisite is falsum, and the definiens is the zero-ary verum assertion.
-- The two major L obligations are therefore ex-falso obligations, while the
-- complete p.145 side-condition sharing is retained literally.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969ObjectVariableMarkWordsExact as ObjectSyntax
import DASHI.Foundations.Wette1969Rule915PredicateProducerExact as Rule915
import DASHI.Foundations.Wette1969Rule915LaterPremiseTemplatesExact as Later

WordTerm = Signature.WordTerm

zeroWord emptyWord oneWord : WordTerm
zeroWord = Signature.constantWordTerm Signature.zeroConstant
emptyWord = Signature.constantWordTerm Signature.emptyConstant
oneWord = Signature.unaryWordTerm Signature.successorFunctor refl zeroWord

verumWord falsumWord : WordTerm
verumWord = Signature.constantWordTerm Signature.verumConstant
falsumWord = Signature.constantWordTerm Signature.falsumConstant

juxtapose : WordTerm → WordTerm → WordTerm
juxtapose u v = Signature.binaryWordTerm Signature.juxtapositionFunctor refl u v

implication : WordTerm → WordTerm → WordTerm
implication u v = Signature.binaryWordTerm Signature.implicationFunctor refl u v

conjunction : WordTerm → WordTerm → WordTerm
conjunction u v = Signature.binaryWordTerm Signature.conjunctionFunctor refl u v

generalize : WordTerm → WordTerm → WordTerm
generalize u v = Signature.binaryWordTerm Signature.generalizationFunctor refl u v

mark0 mark1 : WordTerm
mark0 = ObjectSyntax.predicateMarkWord zeroWord zeroWord
mark1 = ObjectSyntax.predicateMarkWord zeroWord oneWord

falseAssertion trueAssertion markAssertion : WordTerm
falseAssertion = juxtapose falsumWord emptyWord
trueAssertion = juxtapose verumWord emptyWord
markAssertion = juxtapose mark0 emptyWord

body16 : WordTerm
body16 = implication falseAssertion (implication trueAssertion markAssertion)

body17 : WordTerm
body17 = implication falseAssertion (implication body16 markAssertion)

sameDirection : WordTerm
sameDirection = implication trueAssertion trueAssertion

directionPair : WordTerm
directionPair = conjunction sameDirection sameDirection

body26 : WordTerm
body26 = implication falseAssertion (implication trueAssertion directionPair)

premise18Consequent : WordTerm
premise18Consequent = implication body17 (implication falseAssertion markAssertion)

premise27Consequent : WordTerm
premise27Consequent = implication falseAssertion (implication body26 directionPair)

context09 : WordTerm
context09 = juxtapose falseAssertion (juxtapose falsumWord verumWord)

context14 : WordTerm
context14 = juxtapose emptyWord (juxtapose falsumWord verumWord)

markPair : WordTerm
markPair = juxtapose mark0 mark1

canonicalFirstSeven : Rule915.Rule915FirstSevenParameters
canonicalFirstSeven =
  Rule915.rule915FirstSevenParameters
    zeroWord zeroWord mark0 emptyWord falsumWord verumWord
    trueAssertion falseAssertion

canonicalLater : Later.Rule915LaterParameters
canonicalLater =
  Later.rule915LaterParameters
    zeroWord
    falseAssertion
    trueAssertion
    mark0 mark0 mark0 mark1
    emptyWord emptyWord emptyWord
    falsumWord verumWord
    context09
    emptyWord context14
    markPair context09
    emptyWord
    (generalize emptyWord body16) body16
    (generalize emptyWord body17) body17
    (generalize emptyWord body26) body26
    trueAssertion trueAssertion
    premise18Consequent premise27Consequent

record Wette1969Rule915ZeroArityFalsumInstanceBoundary : Set where
  constructor wette1969Rule915ZeroArityFalsumInstanceBoundary
  field
    arityIsZero : Bool
    arityIsZeroIsTrue : arityIsZero ≡ true
    allThreeRule915VariableTuplesAreEmpty : Bool
    allThreeRule915VariableTuplesAreEmptyIsTrue : allThreeRule915VariableTuplesAreEmpty ≡ true
    definitionPrerequisiteIsFalseAssertion : Bool
    definitionPrerequisiteIsFalseAssertionIsTrue : definitionPrerequisiteIsFalseAssertion ≡ true
    definiensHasNoPredicateMarkOccurrence : Bool
    definiensHasNoPredicateMarkOccurrenceIsTrue : definiensHasNoPredicateMarkOccurrence ≡ true
    bothMajorObligationsHaveFalseAntecedent : Bool
    bothMajorObligationsHaveFalseAntecedentIsTrue : bothMajorObligationsHaveFalseAntecedent ≡ true

canonicalWette1969Rule915ZeroArityFalsumInstanceBoundary :
  Wette1969Rule915ZeroArityFalsumInstanceBoundary
canonicalWette1969Rule915ZeroArityFalsumInstanceBoundary =
  wette1969Rule915ZeroArityFalsumInstanceBoundary true refl true refl true refl true refl true refl
