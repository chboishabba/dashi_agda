module DASHI.Foundations.Wette1969CriticalPremiseConcreteProducerChainExact where

------------------------------------------------------------------------
-- CONCRETE HISTORICAL PRODUCER CHAIN FOR 9.3.24/25 PREMISES 1--3
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969JudgementConstructorsExact as Judgment
import DASHI.Foundations.Wette1969Rule9324x25PremiseTemplateExact as CriticalRule
import DASHI.Foundations.Wette1969DependentTwoStageSubstitutionExact as TwoStage
import DASHI.Foundations.Wette1969Rule828To9324x25DerivationExact as Weld
import DASHI.Foundations.Wette1969Rule915PredicateProducerExact as Rule915
import DASHI.Foundations.Wette1969Rule83TupleDerivationExact as Rule83
import DASHI.Foundations.Wette1969Rule8112FreshnessDerivationExact as Rule8112
import DASHI.Foundations.Wette1969CriticalPremiseLocalDerivationExact as Local
import DASHI.Foundations.Wette1969ProofCarryingRuleApplicationExact as Historical
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite

WordTerm = Signature.WordTerm
Context = Finite.DerivationContext

historicalSystem = Local.historicalSystem

recursivePredicateOf : TwoStage.DependentTwoStageSubstitution → WordTerm
recursivePredicateOf stages =
  TwoStage.recursivePredicate (TwoStage.second stages)

parametersOf :
  WordTerm → WordTerm → TwoStage.DependentTwoStageSubstitution →
  CriticalRule.Rule9324x25PremiseParameters
parametersOf = Weld.criticalPremiseParametersFromStages

after915 :
  (initial : Context) →
  (transcription : Rule915.Rule915PremiseTranscription) →
  (arity : WordTerm) →
  (stages : TwoStage.DependentTwoStageSubstitution) →
  Historical.PremisesHold
    Finite.finiteHistoricalContextSystem
    initial
    (Rule915.rule9-1-5 transcription arity (recursivePredicateOf stages)) →
  Context
after915 initial transcription arity stages evidence =
  PCRA.applySelected historicalSystem
    (Rule915.selectRule915
      initial transcription arity (recursivePredicateOf stages) evidence)

after832 :
  (initial : Context) →
  (transcription : Rule915.Rule915PremiseTranscription) →
  (arity : WordTerm) →
  (stages : TwoStage.DependentTwoStageSubstitution) →
  (e915 :
    Historical.PremisesHold
      Finite.finiteHistoricalContextSystem
      initial
      (Rule915.rule9-1-5 transcription arity (recursivePredicateOf stages))) →
  (priorArity priorTuple variable : WordTerm) →
  Judgment.naturalVariable variable Finite.∈Context
    (after915 initial transcription arity stages e915) →
  Judgment.freeForSyntax variable priorTuple Finite.∈Context
    (after915 initial transcription arity stages e915) →
  Judgment.distinctVariableTuple priorArity priorTuple Finite.∈Context
    (after915 initial transcription arity stages e915) →
  Context
after832
  initial transcription arity stages e915
  priorArity priorTuple variable variableEvidence tupleFreshness priorTupleEvidence =
  PCRA.applySelected historicalSystem
    (Rule83.selectRule832
      (after915 initial transcription arity stages e915)
      priorArity priorTuple variable
      variableEvidence tupleFreshness priorTupleEvidence)

concreteFirstThreeProducerChain :
  (initial : Context) →
  (arity freshnessContext : WordTerm) →
  (stages : TwoStage.DependentTwoStageSubstitution) →
  (transcription : Rule915.Rule915PremiseTranscription) →
  (e915 :
    Historical.PremisesHold
      Finite.finiteHistoricalContextSystem
      initial
      (Rule915.rule9-1-5 transcription arity (recursivePredicateOf stages))) →
  (priorArity priorTuple variable : WordTerm) →
  arity ≡ Rule83.successor priorArity →
  TwoStage.newTuple (TwoStage.first stages)
    ≡ Rule83.juxtapose priorTuple variable →
  (variableEvidence :
    Judgment.naturalVariable variable Finite.∈Context
      (after915 initial transcription arity stages e915)) →
  (tupleFreshness :
    Judgment.freeForSyntax variable priorTuple Finite.∈Context
      (after915 initial transcription arity stages e915)) →
  (priorTupleEvidence :
    Judgment.distinctVariableTuple priorArity priorTuple Finite.∈Context
      (after915 initial transcription arity stages e915)) →
  (priorTupleFreshForCriticalContext :
    Judgment.freeForSyntax priorTuple freshnessContext Finite.∈Context
      (after832
        initial transcription arity stages e915
        priorArity priorTuple variable
        variableEvidence tupleFreshness priorTupleEvidence)) →
  (newVariableFreshForCriticalContext :
    Judgment.freeForSyntax variable freshnessContext Finite.∈Context
      (after832
        initial transcription arity stages e915
        priorArity priorTuple variable
        variableEvidence tupleFreshness priorTupleEvidence)) →
  Local.FirstThreeCriticalProducerChain
    initial
    (Weld.criticalPremiseParametersFromStages arity freshnessContext stages)
concreteFirstThreeProducerChain
  initial arity freshnessContext stages transcription e915
  priorArity priorTuple variable arityEquality tupleEquality
  variableEvidence tupleFreshness priorTupleEvidence
  priorTupleFreshForCriticalContext newVariableFreshForCriticalContext =
  Local.firstThreeCriticalProducerChain
    predicateTrace
    predicateProduced
    tupleTrace
    tupleProduced
    freshnessTrace
    freshnessProduced
  where
    selected915 =
      Rule915.selectRule915
        initial transcription arity (recursivePredicateOf stages) e915

    predicateTrace = PCRA.choose selected915 PCRA.done

    predicateProduced :
      Judgment.predicateSchema arity (recursivePredicateOf stages)
        Finite.∈Context
        (PCRA.runCertifiedTrace historicalSystem predicateTrace)
    predicateProduced = Finite.here

    context915 = after915 initial transcription arity stages e915

    selected832 =
      Rule83.selectRule832
        context915
        priorArity priorTuple variable
        variableEvidence tupleFreshness priorTupleEvidence

    tupleTrace = PCRA.choose selected832 PCRA.done

    tupleProduced :
      Judgment.distinctVariableTuple
        arity
        (TwoStage.newTuple (TwoStage.first stages))
        Finite.∈Context
        (PCRA.runCertifiedTrace historicalSystem tupleTrace)
    tupleProduced rewrite arityEquality | tupleEquality = Finite.here

    context832 =
      after832
        initial transcription arity stages e915
        priorArity priorTuple variable
        variableEvidence tupleFreshness priorTupleEvidence

    selected8112 =
      Rule8112.selectRule8112
        context832
        priorTuple variable freshnessContext
        priorTupleFreshForCriticalContext
        newVariableFreshForCriticalContext

    freshnessTrace = PCRA.choose selected8112 PCRA.done

    freshnessProduced :
      Judgment.freeForSyntax
        (TwoStage.newTuple (TwoStage.first stages))
        freshnessContext
        Finite.∈Context
        (PCRA.runCertifiedTrace historicalSystem freshnessTrace)
    freshnessProduced rewrite tupleEquality = Finite.here

record Wette1969CriticalPremiseConcreteProducerBoundary : Set where
  constructor wette1969CriticalPremiseConcreteProducerBoundary
  field
    premise1CanBeGeneratedByCertifiedRule915 : Bool
    premise1CanBeGeneratedByCertifiedRule915IsTrue :
      premise1CanBeGeneratedByCertifiedRule915 ≡ true

    premise2CanBeGeneratedByCertifiedRule832 : Bool
    premise2CanBeGeneratedByCertifiedRule832IsTrue :
      premise2CanBeGeneratedByCertifiedRule832 ≡ true

    premise3CanBeGeneratedByCertifiedRule8112 : Bool
    premise3CanBeGeneratedByCertifiedRule8112IsTrue :
      premise3CanBeGeneratedByCertifiedRule8112 ≡ true

    firstThreeProducerRulesComposeIntoCriticalChain : Bool
    firstThreeProducerRulesComposeIntoCriticalChainIsTrue :
      firstThreeProducerRulesComposeIntoCriticalChain ≡ true

    producerSideConditionsAreAutomaticallyTrueWithoutEvidence : Bool
    producerSideConditionsAreAutomaticallyTrueWithoutEvidenceIsFalse :
      producerSideConditionsAreAutomaticallyTrueWithoutEvidence ≡ false

canonicalWette1969CriticalPremiseConcreteProducerBoundary :
  Wette1969CriticalPremiseConcreteProducerBoundary
canonicalWette1969CriticalPremiseConcreteProducerBoundary =
  wette1969CriticalPremiseConcreteProducerBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
