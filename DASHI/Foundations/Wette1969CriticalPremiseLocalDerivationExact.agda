module DASHI.Foundations.Wette1969CriticalPremiseLocalDerivationExact where

------------------------------------------------------------------------
-- WETTE 1969 LOCALLY GENERATED 9.3.24/25 PREMISE CHAIN
--
-- This module composes the source-recovered producer lanes:
--   premise 1: predicate-schema production (ultimately 9.1.5),
--   premise 2: distinct variable-tuple production (8.3.1/2),
--   premise 3: tuple freshness production (8.1.12/13 family),
--   premise 4: paired II production (8.2.8),
-- then consumes all four with 9.3.24 or 9.3.25.
--
-- The important change from the previous weld is that the first three critical
-- premises are represented by *certified producer traces*, not membership facts
-- assumed at the initial context.  Their conclusions persist through all later
-- producer traces by the existing monotone-closure theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969CriticalRuleDependencyExact as Critical
import DASHI.Foundations.Wette1969Rule9324x25PremiseTemplateExact as CriticalRule
import DASHI.Foundations.Wette1969DependentTwoStageSubstitutionExact as TwoStage
import DASHI.Foundations.Wette1969Rule828To9324x25DerivationExact as Weld
import DASHI.Foundations.Wette1969ProofCarryingRuleApplicationExact as Historical
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite
import DASHI.Foundations.Wette1969DerivationClosureExact as Closure

WordTerm = Signature.WordTerm
Formula = Signature.Formula
Context = Finite.DerivationContext

historicalSystem =
  Historical.historicalRuleApplicationSystem Finite.finiteHistoricalContextSystem

------------------------------------------------------------------------
-- Dependent producer chain for the first three critical premises.
------------------------------------------------------------------------

record FirstThreeCriticalProducerChain
    (initial : Context)
    (parameters : CriticalRule.Rule9324x25PremiseParameters) : Set₁ where
  constructor firstThreeCriticalProducerChain
  field
    predicateTrace : PCRA.CertifiedRuleTrace historicalSystem initial
    predicateProduced :
      CriticalRule.premiseAt parameters Critical.recursivePredicateFormation
        Finite.∈Context
        (PCRA.runCertifiedTrace historicalSystem predicateTrace)

    tupleTrace :
      PCRA.CertifiedRuleTrace historicalSystem
        (PCRA.runCertifiedTrace historicalSystem predicateTrace)
    tupleProduced :
      CriticalRule.premiseAt parameters Critical.freshVariableTupleFormation
        Finite.∈Context
        (PCRA.runCertifiedTrace historicalSystem tupleTrace)

    freshnessTrace :
      PCRA.CertifiedRuleTrace historicalSystem
        (PCRA.runCertifiedTrace historicalSystem tupleTrace)
    freshnessProduced :
      CriticalRule.premiseAt parameters Critical.variableFreshnessCondition
        Finite.∈Context
        (PCRA.runCertifiedTrace historicalSystem freshnessTrace)

open FirstThreeCriticalProducerChain public

producerTarget :
  {initial : Context} →
  {parameters : CriticalRule.Rule9324x25PremiseParameters} →
  FirstThreeCriticalProducerChain initial parameters →
  Context
producerTarget chain =
  PCRA.runCertifiedTrace historicalSystem (freshnessTrace chain)

predicateAvailableAtProducerTarget :
  {initial : Context} →
  {parameters : CriticalRule.Rule9324x25PremiseParameters} →
  (chain : FirstThreeCriticalProducerChain initial parameters) →
  CriticalRule.premiseAt parameters Critical.recursivePredicateFormation
    Finite.∈Context producerTarget chain
predicateAvailableAtProducerTarget chain =
  Closure.certifiedTracePreservesPriorFormula
    (freshnessTrace chain)
    (CriticalRule.premiseAt _ Critical.recursivePredicateFormation)
    (Closure.certifiedTracePreservesPriorFormula
      (tupleTrace chain)
      (CriticalRule.premiseAt _ Critical.recursivePredicateFormation)
      (predicateProduced chain))

freshTupleAvailableAtProducerTarget :
  {initial : Context} →
  {parameters : CriticalRule.Rule9324x25PremiseParameters} →
  (chain : FirstThreeCriticalProducerChain initial parameters) →
  CriticalRule.premiseAt parameters Critical.freshVariableTupleFormation
    Finite.∈Context producerTarget chain
freshTupleAvailableAtProducerTarget chain =
  Closure.certifiedTracePreservesPriorFormula
    (freshnessTrace chain)
    (CriticalRule.premiseAt _ Critical.freshVariableTupleFormation)
    (tupleProduced chain)

freshnessAvailableAtProducerTarget :
  {initial : Context} →
  {parameters : CriticalRule.Rule9324x25PremiseParameters} →
  (chain : FirstThreeCriticalProducerChain initial parameters) →
  CriticalRule.premiseAt parameters Critical.variableFreshnessCondition
    Finite.∈Context producerTarget chain
freshnessAvailableAtProducerTarget chain = freshnessProduced chain

firstThreeAvailableAtProducerTarget :
  {initial : Context} →
  {parameters : CriticalRule.Rule9324x25PremiseParameters} →
  (chain : FirstThreeCriticalProducerChain initial parameters) →
  Weld.FirstThreeCriticalPremises (producerTarget chain) parameters
firstThreeAvailableAtProducerTarget chain =
  Weld.firstThreeCriticalPremises
    (predicateAvailableAtProducerTarget chain)
    (freshTupleAvailableAtProducerTarget chain)
    (freshnessAvailableAtProducerTarget chain)

------------------------------------------------------------------------
-- Sequential II premises may already be available before the producer chain.
-- Monotonicity carries them through all three producer traces to the point at
-- which rule 8.2.8 is applied.
------------------------------------------------------------------------

firstIIAvailableAtProducerTarget :
  {initial : Context} →
  {parameters : CriticalRule.Rule9324x25PremiseParameters} →
  (chain : FirstThreeCriticalProducerChain initial parameters) →
  (stages : TwoStage.DependentTwoStageSubstitution) →
  TwoStage.firstStageII (TwoStage.first stages) Finite.∈Context initial →
  TwoStage.firstStageII (TwoStage.first stages)
    Finite.∈Context producerTarget chain
firstIIAvailableAtProducerTarget chain stages evidence =
  Closure.certifiedTracePreservesPriorFormula
    (freshnessTrace chain)
    (TwoStage.firstStageII (TwoStage.first stages))
    (Closure.certifiedTracePreservesPriorFormula
      (tupleTrace chain)
      (TwoStage.firstStageII (TwoStage.first stages))
      (Closure.certifiedTracePreservesPriorFormula
        (predicateTrace chain)
        (TwoStage.firstStageII (TwoStage.first stages))
        evidence))

secondIIAvailableAtProducerTarget :
  {initial : Context} →
  {parameters : CriticalRule.Rule9324x25PremiseParameters} →
  (chain : FirstThreeCriticalProducerChain initial parameters) →
  (stages : TwoStage.DependentTwoStageSubstitution) →
  TwoStage.secondStageII (TwoStage.first stages) (TwoStage.second stages)
    Finite.∈Context initial →
  TwoStage.secondStageII (TwoStage.first stages) (TwoStage.second stages)
    Finite.∈Context producerTarget chain
secondIIAvailableAtProducerTarget chain stages evidence =
  Closure.certifiedTracePreservesPriorFormula
    (freshnessTrace chain)
    (TwoStage.secondStageII (TwoStage.first stages) (TwoStage.second stages))
    (Closure.certifiedTracePreservesPriorFormula
      (tupleTrace chain)
      (TwoStage.secondStageII (TwoStage.first stages) (TwoStage.second stages))
      (Closure.certifiedTracePreservesPriorFormula
        (predicateTrace chain)
        (TwoStage.secondStageII (TwoStage.first stages) (TwoStage.second stages))
        evidence))

------------------------------------------------------------------------
-- Complete local critical traces.
--
-- All first-three evidence comes from producer traces.  Premise 4 then comes
-- from rule 8.2.8 at their common target.  Certified-trace append keeps each
-- continuation indexed by the actual state produced by the preceding trace.
------------------------------------------------------------------------

locallyGeneratedTrace9324 :
  (initial : Context) →
  (arity freshnessContext : WordTerm) →
  (stages : TwoStage.DependentTwoStageSubstitution) →
  (conclusions : CriticalRule.Rule9324x25ConclusionParameters) →
  (chain :
    FirstThreeCriticalProducerChain
      initial
      (Weld.criticalPremiseParametersFromStages arity freshnessContext stages)) →
  TwoStage.firstStageII (TwoStage.first stages) Finite.∈Context initial →
  TwoStage.secondStageII (TwoStage.first stages) (TwoStage.second stages)
    Finite.∈Context initial →
  PCRA.CertifiedRuleTrace historicalSystem initial
locallyGeneratedTrace9324
  initial arity freshnessContext stages conclusions chain firstEvidence secondEvidence =
  PCRA.appendCertifiedTrace
    (predicateTrace chain)
    (PCRA.appendCertifiedTrace
      (tupleTrace chain)
      (PCRA.appendCertifiedTrace
        (freshnessTrace chain)
        (Weld.trace828Then9324
          (producerTarget chain)
          arity freshnessContext stages conclusions
          (firstIIAvailableAtProducerTarget chain stages firstEvidence)
          (secondIIAvailableAtProducerTarget chain stages secondEvidence)
          (firstThreeAvailableAtProducerTarget chain))))

locallyGeneratedTrace9325 :
  (initial : Context) →
  (arity freshnessContext : WordTerm) →
  (stages : TwoStage.DependentTwoStageSubstitution) →
  (conclusions : CriticalRule.Rule9324x25ConclusionParameters) →
  (chain :
    FirstThreeCriticalProducerChain
      initial
      (Weld.criticalPremiseParametersFromStages arity freshnessContext stages)) →
  TwoStage.firstStageII (TwoStage.first stages) Finite.∈Context initial →
  TwoStage.secondStageII (TwoStage.first stages) (TwoStage.second stages)
    Finite.∈Context initial →
  PCRA.CertifiedRuleTrace historicalSystem initial
locallyGeneratedTrace9325
  initial arity freshnessContext stages conclusions chain firstEvidence secondEvidence =
  PCRA.appendCertifiedTrace
    (predicateTrace chain)
    (PCRA.appendCertifiedTrace
      (tupleTrace chain)
      (PCRA.appendCertifiedTrace
        (freshnessTrace chain)
        (Weld.trace828Then9325
          (producerTarget chain)
          arity freshnessContext stages conclusions
          (firstIIAvailableAtProducerTarget chain stages firstEvidence)
          (secondIIAvailableAtProducerTarget chain stages secondEvidence)
          (firstThreeAvailableAtProducerTarget chain))))

record Wette1969CriticalPremiseLocalDerivationBoundary : Set where
  constructor wette1969CriticalPremiseLocalDerivationBoundary
  field
    firstThreeCriticalPremisesCanComeFromCertifiedProducerTraces : Bool
    firstThreeCriticalPremisesCanComeFromCertifiedProducerTracesIsTrue :
      firstThreeCriticalPremisesCanComeFromCertifiedProducerTraces ≡ true

    producerConclusionsPersistToCommonCriticalContext : Bool
    producerConclusionsPersistToCommonCriticalContextIsTrue :
      producerConclusionsPersistToCommonCriticalContext ≡ true

    completeProducer828CriticalTracesNowComposeDependently : Bool
    completeProducer828CriticalTracesNowComposeDependentlyIsTrue :
      completeProducer828CriticalTracesNowComposeDependently ≡ true

    firstThreeCriticalPremisesMustBeInitialContextMembershipFacts : Bool
    firstThreeCriticalPremisesMustBeInitialContextMembershipFactsIsFalse :
      firstThreeCriticalPremisesMustBeInitialContextMembershipFacts ≡ false

    producerTraceExistenceAutomaticallyDischargesProducerPremises : Bool
    producerTraceExistenceAutomaticallyDischargesProducerPremisesIsFalse :
      producerTraceExistenceAutomaticallyDischargesProducerPremises ≡ false

canonicalWette1969CriticalPremiseLocalDerivationBoundary :
  Wette1969CriticalPremiseLocalDerivationBoundary
canonicalWette1969CriticalPremiseLocalDerivationBoundary =
  wette1969CriticalPremiseLocalDerivationBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
