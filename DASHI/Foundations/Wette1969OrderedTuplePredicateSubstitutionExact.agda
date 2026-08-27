module DASHI.Foundations.Wette1969OrderedTuplePredicateSubstitutionExact where

------------------------------------------------------------------------
-- WETTE 1969 ORDERED TUPLE -> PREDICATE-MARK SUBSTITUTION
--
-- Eduard Wette,
-- "Definition eines (relativ vollständigen) formalen Systems konstruktiver
-- Arithmetik", Foundations of Mathematics, Springer 1969, pp. 130--195.
-- DOI: 10.1007/978-3-642-86745-3_9
--
-- Section 1.632 states that for rule 9.3.24/25 premise 4 the relevant
-- substitutions are ordered: first replace the old variable tuple by the new
-- tuple, then replace the predicate mark by the recursively defined predicate.
--
-- The historical syntax already exposes two distinct syntactic classes that let
-- us model a bounded exact fragment of that order:
--   * rule-schematic WordVariable occurrences;
--   * the distinguished predicateMarkKernel constant.
--
-- We therefore combine the existing schematic-variable instantiator with a
-- structural predicate-mark replacement.  This is still not Wette's complete
-- binding-aware four-place substitution relation, but it is an executable
-- two-stage evaluator with an exact non-commutation witness showing why the
-- source-stated order cannot be erased in general.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969SchematicSubstitutionFreshnessExact as Schematic

WordTerm = Signature.WordTerm

------------------------------------------------------------------------
-- Structural replacement of the distinguished predicate-mark constant.
------------------------------------------------------------------------

replacePredicateMark : WordTerm → WordTerm → WordTerm
replacePredicateMark replacement (Signature.variableWordTerm variable) =
  Signature.variableWordTerm variable
replacePredicateMark replacement
  (Signature.constantWordTerm Signature.predicateMarkKernel) = replacement
replacePredicateMark replacement
  (Signature.constantWordTerm Signature.emptyConstant) =
  Signature.constantWordTerm Signature.emptyConstant
replacePredicateMark replacement
  (Signature.constantWordTerm Signature.zeroConstant) =
  Signature.constantWordTerm Signature.zeroConstant
replacePredicateMark replacement
  (Signature.constantWordTerm Signature.variableKernel) =
  Signature.constantWordTerm Signature.variableKernel
replacePredicateMark replacement
  (Signature.constantWordTerm Signature.orderPredicateConstant) =
  Signature.constantWordTerm Signature.orderPredicateConstant
replacePredicateMark replacement
  (Signature.constantWordTerm Signature.verumConstant) =
  Signature.constantWordTerm Signature.verumConstant
replacePredicateMark replacement
  (Signature.constantWordTerm Signature.falsumConstant) =
  Signature.constantWordTerm Signature.falsumConstant
replacePredicateMark replacement
  (Signature.unaryWordTerm functor arity term) =
  Signature.unaryWordTerm functor arity
    (replacePredicateMark replacement term)
replacePredicateMark replacement
  (Signature.binaryWordTerm functor arity left right) =
  Signature.binaryWordTerm functor arity
    (replacePredicateMark replacement left)
    (replacePredicateMark replacement right)

------------------------------------------------------------------------
-- Source-ordered and reversed two-stage evaluators.
------------------------------------------------------------------------

orderedTupleThenPredicate :
  Schematic.SubstitutionEnvironment →
  WordTerm →
  WordTerm →
  WordTerm
orderedTupleThenPredicate tupleEnvironment predicateReplacement source =
  replacePredicateMark predicateReplacement
    (Schematic.instantiateWordTerm tupleEnvironment source)

reversedPredicateThenTuple :
  Schematic.SubstitutionEnvironment →
  WordTerm →
  WordTerm →
  WordTerm
reversedPredicateThenTuple tupleEnvironment predicateReplacement source =
  Schematic.instantiateWordTerm tupleEnvironment
    (replacePredicateMark predicateReplacement source)

------------------------------------------------------------------------
-- Exact order-sensitivity witness in the bounded structural model.
--
-- Let every schematic variable instantiate to the predicate mark and let the
-- predicate mark itself then be replaced by zero.  Starting from a schematic
-- variable, source order yields zero; reversed order leaves the newly inserted
-- predicate mark untouched by the already-completed predicate replacement.
------------------------------------------------------------------------

allPredicateMarks : Schematic.SubstitutionEnvironment
allPredicateMarks variable =
  Signature.constantWordTerm Signature.predicateMarkKernel

zeroReplacement : WordTerm
zeroReplacement = Signature.constantWordTerm Signature.zeroConstant

sampleSource : WordTerm
sampleSource = Signature.variableWordTerm Data.Fin.zero

orderedSampleReducesToZero :
  orderedTupleThenPredicate allPredicateMarks zeroReplacement sampleSource
    ≡ Signature.constantWordTerm Signature.zeroConstant
orderedSampleReducesToZero = refl

reversedSampleLeavesPredicateMark :
  reversedPredicateThenTuple allPredicateMarks zeroReplacement sampleSource
    ≡ Signature.constantWordTerm Signature.predicateMarkKernel
reversedSampleLeavesPredicateMark = refl

zeroWordNotPredicateMarkWord :
  Signature.constantWordTerm Signature.zeroConstant
    ≡ Signature.constantWordTerm Signature.predicateMarkKernel →
  ⊥
zeroWordNotPredicateMarkWord ()

orderedAndReversedCanDiffer :
  orderedTupleThenPredicate allPredicateMarks zeroReplacement sampleSource
    ≡ reversedPredicateThenTuple allPredicateMarks zeroReplacement sampleSource →
  ⊥
orderedAndReversedCanDiffer equality =
  zeroWordNotPredicateMarkWord equality

------------------------------------------------------------------------
-- Certificate carrying exactly the source-ordered computation.
------------------------------------------------------------------------

record OrderedTuplePredicateSubstitutionCertificate : Set where
  constructor orderedTuplePredicateSubstitutionCertificate
  field
    tupleEnvironment : Schematic.SubstitutionEnvironment
    predicateReplacement : WordTerm
    source : WordTerm
    result : WordTerm
    evaluatesInSourceOrder :
      orderedTupleThenPredicate
        tupleEnvironment predicateReplacement source
      ≡ result

open OrderedTuplePredicateSubstitutionCertificate public

canonicalOrderedCertificate :
  (tupleEnvironment : Schematic.SubstitutionEnvironment) →
  (predicateReplacement source : WordTerm) →
  OrderedTuplePredicateSubstitutionCertificate
canonicalOrderedCertificate tupleEnvironment predicateReplacement source =
  orderedTuplePredicateSubstitutionCertificate
    tupleEnvironment
    predicateReplacement
    source
    (orderedTupleThenPredicate tupleEnvironment predicateReplacement source)
    refl

record Wette1969OrderedTuplePredicateSubstitutionBoundary : Set where
  constructor wette1969OrderedTuplePredicateSubstitutionBoundary
  field
    tupleThenPredicateOrderNowExecutable : Bool
    tupleThenPredicateOrderNowExecutableIsTrue :
      tupleThenPredicateOrderNowExecutable ≡ true

    structuralOrderSensitivityWitnessNowExists : Bool
    structuralOrderSensitivityWitnessNowExistsIsTrue :
      structuralOrderSensitivityWitnessNowExists ≡ true

    sourceOrderRequirementNowHasConcreteComputationalWitness : Bool
    sourceOrderRequirementNowHasConcreteComputationalWitnessIsTrue :
      sourceOrderRequirementNowHasConcreteComputationalWitness ≡ true

    evaluatorAlreadyImplementsBindingAwareCaptureAvoidance : Bool
    evaluatorAlreadyImplementsBindingAwareCaptureAvoidanceIsFalse :
      evaluatorAlreadyImplementsBindingAwareCaptureAvoidance ≡ false

    boundedStructuralNonCommutationIsFullHistoricalSubstitutionTheorem : Bool
    boundedStructuralNonCommutationIsFullHistoricalSubstitutionTheoremIsFalse :
      boundedStructuralNonCommutationIsFullHistoricalSubstitutionTheorem ≡ false

canonicalWette1969OrderedTuplePredicateSubstitutionBoundary :
  Wette1969OrderedTuplePredicateSubstitutionBoundary
canonicalWette1969OrderedTuplePredicateSubstitutionBoundary =
  wette1969OrderedTuplePredicateSubstitutionBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
