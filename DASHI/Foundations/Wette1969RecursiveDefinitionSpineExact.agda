module DASHI.Foundations.Wette1969RecursiveDefinitionSpineExact where

------------------------------------------------------------------------
-- END-TO-END LOCAL RECURSIVE-DEFINITION SPINE
--
-- Factored 9.1.5 obligation producers -> certified 9.1.5 -> 8.3.2 tuple ->
-- 8.1.12 freshness -> certified two-stage II -> 8.2.8 -> 9.3.24/25.
--
-- This is not a derivation from the empty context.  It is the strongest local
-- source-faithful composition currently justified: the remaining frontier is
-- pushed into the producer traces/side conditions for the two 9.1.5 L-blocks.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969JudgementConstructorsExact as Judgment
import DASHI.Foundations.Wette1969Rule915PredicateProducerExact as Rule915
import DASHI.Foundations.Wette1969Rule915ObligationProducerChainExact as Obligations
import DASHI.Foundations.Wette1969Rule83TupleDerivationExact as Rule83
import DASHI.Foundations.Wette1969Rule8112FreshnessDerivationExact as Rule8112
import DASHI.Foundations.Wette1969Rule828To9324x25DerivationExact as Weld
import DASHI.Foundations.Wette1969CriticalPremiseLocalDerivationExact as Local
import DASHI.Foundations.Wette1969CertifiedTwoStageIIDerivationExact as CertifiedII
import DASHI.Foundations.Wette1969DependentTwoStageSubstitutionExact as TwoStage
import DASHI.Foundations.Wette1969FullyGeneratedCriticalApplicationExact as Fully
import DASHI.Foundations.Wette1969Rule9324x25PremiseTemplateExact as CriticalRule
import DASHI.Foundations.Wette1969ProofCarryingRuleApplicationExact as Historical
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite

WordTerm = Signature.WordTerm
Context = Finite.DerivationContext

historicalSystem = Local.historicalSystem

record RecursiveDefinitionSpineInputs
    (initial : Context)
    (transcription : Rule915.Rule915PremiseTranscription)
    (arity freshnessContext : WordTerm)
    (stages : TwoStage.DependentTwoStageSubstitution) : Set₁ where
  constructor recursiveDefinitionSpineInputs
  field
    obligationChain :
      Obligations.Rule915ObligationProducerChain initial transcription

    priorArity : WordTerm
    priorTuple : WordTerm
    newVariable : WordTerm

    arityIsSuccessor : arity ≡ Rule83.successor priorArity
    freshTupleIsExtension :
      TwoStage.newTuple (TwoStage.first stages)
        ≡ Rule83.juxtapose priorTuple newVariable

    variableEvidenceAfter915 :
      Judgment.naturalVariable newVariable Finite.∈Context after915
    tupleFreshnessAfter915 :
      Judgment.freeForSyntax newVariable priorTuple Finite.∈Context after915
    priorTupleEvidenceAfter915 :
      Judgment.distinctVariableTuple priorArity priorTuple Finite.∈Context after915

    priorTupleFreshForCriticalContext :
      Judgment.freeForSyntax priorTuple freshnessContext Finite.∈Context after832
    newVariableFreshForCriticalContext :
      Judgment.freeForSyntax newVariable freshnessContext Finite.∈Context after832

    sequentialII :
      CertifiedII.CertifiedTwoStageIIDerivation afterFreshness stages
  where
    recursivePredicate = TwoStage.recursivePredicate (TwoStage.second stages)
    predicateTrace =
      Obligations.completeObligationThen915Trace
        arity recursivePredicate obligationChain
    after915 = PCRA.runCertifiedTrace historicalSystem predicateTrace

    tupleSelected =
      Rule83.selectRule832
        after915 priorArity priorTuple newVariable
        variableEvidenceAfter915 tupleFreshnessAfter915 priorTupleEvidenceAfter915
    tupleTrace = PCRA.choose tupleSelected PCRA.done
    after832 = PCRA.runCertifiedTrace historicalSystem tupleTrace

    freshnessSelected =
      Rule8112.selectRule8112
        after832 priorTuple newVariable freshnessContext
        priorTupleFreshForCriticalContext newVariableFreshForCriticalContext
    freshnessTrace = PCRA.choose freshnessSelected PCRA.done
    afterFreshness = PCRA.runCertifiedTrace historicalSystem freshnessTrace

open RecursiveDefinitionSpineInputs public

predicateTrace :
  {initial : Context} →
  {transcription : Rule915.Rule915PremiseTranscription} →
  {arity freshnessContext : WordTerm} →
  {stages : TwoStage.DependentTwoStageSubstitution} →
  RecursiveDefinitionSpineInputs initial transcription arity freshnessContext stages →
  PCRA.CertifiedRuleTrace historicalSystem initial
predicateTrace {arity = arity} {stages = stages} inputs =
  Obligations.completeObligationThen915Trace
    arity
    (TwoStage.recursivePredicate (TwoStage.second stages))
    (obligationChain inputs)

after915 :
  {initial : Context} →
  {transcription : Rule915.Rule915PremiseTranscription} →
  {arity freshnessContext : WordTerm} →
  {stages : TwoStage.DependentTwoStageSubstitution} →
  RecursiveDefinitionSpineInputs initial transcription arity freshnessContext stages → Context
after915 inputs = PCRA.runCertifiedTrace historicalSystem (predicateTrace inputs)

tupleSelected :
  {initial : Context} →
  {transcription : Rule915.Rule915PremiseTranscription} →
  {arity freshnessContext : WordTerm} →
  {stages : TwoStage.DependentTwoStageSubstitution} →
  (inputs : RecursiveDefinitionSpineInputs initial transcription arity freshnessContext stages) →
  PCRA.SelectedRuleApplication historicalSystem (after915 inputs)
tupleSelected inputs =
  Rule83.selectRule832
    (after915 inputs)
    (priorArity inputs)
    (priorTuple inputs)
    (newVariable inputs)
    (variableEvidenceAfter915 inputs)
    (tupleFreshnessAfter915 inputs)
    (priorTupleEvidenceAfter915 inputs)

tupleTrace :
  {initial : Context} →
  {transcription : Rule915.Rule915PremiseTranscription} →
  {arity freshnessContext : WordTerm} →
  {stages : TwoStage.DependentTwoStageSubstitution} →
  (inputs : RecursiveDefinitionSpineInputs initial transcription arity freshnessContext stages) →
  PCRA.CertifiedRuleTrace historicalSystem (after915 inputs)
tupleTrace inputs = PCRA.choose (tupleSelected inputs) PCRA.done

after832 :
  {initial : Context} →
  {transcription : Rule915.Rule915PremiseTranscription} →
  {arity freshnessContext : WordTerm} →
  {stages : TwoStage.DependentTwoStageSubstitution} →
  (inputs : RecursiveDefinitionSpineInputs initial transcription arity freshnessContext stages) → Context
after832 inputs = PCRA.runCertifiedTrace historicalSystem (tupleTrace inputs)

freshnessSelected :
  {initial : Context} →
  {transcription : Rule915.Rule915PremiseTranscription} →
  {arity freshnessContext : WordTerm} →
  {stages : TwoStage.DependentTwoStageSubstitution} →
  (inputs : RecursiveDefinitionSpineInputs initial transcription arity freshnessContext stages) →
  PCRA.SelectedRuleApplication historicalSystem (after832 inputs)
freshnessSelected {freshnessContext = freshnessContext} inputs =
  Rule8112.selectRule8112
    (after832 inputs)
    (priorTuple inputs)
    (newVariable inputs)
    freshnessContext
    (priorTupleFreshForCriticalContext inputs)
    (newVariableFreshForCriticalContext inputs)

freshnessTrace :
  {initial : Context} →
  {transcription : Rule915.Rule915PremiseTranscription} →
  {arity freshnessContext : WordTerm} →
  {stages : TwoStage.DependentTwoStageSubstitution} →
  (inputs : RecursiveDefinitionSpineInputs initial transcription arity freshnessContext stages) →
  PCRA.CertifiedRuleTrace historicalSystem (after832 inputs)
freshnessTrace inputs = PCRA.choose (freshnessSelected inputs) PCRA.done

afterFreshness :
  {initial : Context} →
  {transcription : Rule915.Rule915PremiseTranscription} →
  {arity freshnessContext : WordTerm} →
  {stages : TwoStage.DependentTwoStageSubstitution} →
  (inputs : RecursiveDefinitionSpineInputs initial transcription arity freshnessContext stages) → Context
afterFreshness inputs =
  PCRA.runCertifiedTrace historicalSystem (freshnessTrace inputs)

firstThreeChain :
  {initial : Context} →
  {transcription : Rule915.Rule915PremiseTranscription} →
  {arity freshnessContext : WordTerm} →
  {stages : TwoStage.DependentTwoStageSubstitution} →
  (inputs : RecursiveDefinitionSpineInputs initial transcription arity freshnessContext stages) →
  Local.FirstThreeCriticalProducerChain
    initial
    (Weld.criticalPremiseParametersFromStages arity freshnessContext stages)
firstThreeChain {arity = arity} {freshnessContext} {stages} inputs =
  Local.firstThreeCriticalProducerChain
    (predicateTrace inputs)
    predicateProduced
    (tupleTrace inputs)
    tupleProduced
    (freshnessTrace inputs)
    freshnessProduced
  where
    predicateProduced :
      Judgment.predicateSchema
        arity
        (TwoStage.recursivePredicate (TwoStage.second stages))
        Finite.∈Context after915 inputs
    predicateProduced = Finite.here

    tupleProduced :
      Judgment.distinctVariableTuple
        arity
        (TwoStage.newTuple (TwoStage.first stages))
        Finite.∈Context after832 inputs
    tupleProduced rewrite arityIsSuccessor inputs | freshTupleIsExtension inputs = Finite.here

    freshnessProduced :
      Judgment.freeForSyntax
        (TwoStage.newTuple (TwoStage.first stages))
        freshnessContext
        Finite.∈Context afterFreshness inputs
    freshnessProduced rewrite freshTupleIsExtension inputs = Finite.here

fullyGenerated :
  {initial : Context} →
  {transcription : Rule915.Rule915PremiseTranscription} →
  {arity freshnessContext : WordTerm} →
  {stages : TwoStage.DependentTwoStageSubstitution} →
  (inputs : RecursiveDefinitionSpineInputs initial transcription arity freshnessContext stages) →
  Fully.FullyGeneratedCriticalPremises initial arity freshnessContext stages
fullyGenerated inputs =
  Fully.fullyGeneratedCriticalPremises
    (firstThreeChain inputs)
    (sequentialII inputs)

recursiveDefinitionTrace9324 :
  {initial : Context} →
  {transcription : Rule915.Rule915PremiseTranscription} →
  {arity freshnessContext : WordTerm} →
  {stages : TwoStage.DependentTwoStageSubstitution} →
  (inputs : RecursiveDefinitionSpineInputs initial transcription arity freshnessContext stages) →
  CriticalRule.Rule9324x25ConclusionParameters →
  PCRA.CertifiedRuleTrace historicalSystem initial
recursiveDefinitionTrace9324 inputs conclusions =
  Fully.fullyGeneratedTrace9324 (fullyGenerated inputs) conclusions

recursiveDefinitionTrace9325 :
  {initial : Context} →
  {transcription : Rule915.Rule915PremiseTranscription} →
  {arity freshnessContext : WordTerm} →
  {stages : TwoStage.DependentTwoStageSubstitution} →
  (inputs : RecursiveDefinitionSpineInputs initial transcription arity freshnessContext stages) →
  CriticalRule.Rule9324x25ConclusionParameters →
  PCRA.CertifiedRuleTrace historicalSystem initial
recursiveDefinitionTrace9325 inputs conclusions =
  Fully.fullyGeneratedTrace9325 (fullyGenerated inputs) conclusions

record Wette1969RecursiveDefinitionSpineBoundary : Set where
  constructor wette1969RecursiveDefinitionSpineBoundary
  field
    factored915ObligationsNowFeedCriticalRecursiveApplication : Bool
    factored915ObligationsNowFeedCriticalRecursiveApplicationIsTrue :
      factored915ObligationsNowFeedCriticalRecursiveApplication ≡ true
    rule915PredicateOutputFeedsPremise1WithoutExternalMembership : Bool
    rule915PredicateOutputFeedsPremise1WithoutExternalMembershipIsTrue :
      rule915PredicateOutputFeedsPremise1WithoutExternalMembership ≡ true
    tupleFreshnessAndPairedIIFollowAtActualReachedStates : Bool
    tupleFreshnessAndPairedIIFollowAtActualReachedStatesIsTrue :
      tupleFreshnessAndPairedIIFollowAtActualReachedStates ≡ true
    recursiveSpineIsAlreadyClosedFromEmptyContext : Bool
    recursiveSpineIsAlreadyClosedFromEmptyContextIsFalse :
      recursiveSpineIsAlreadyClosedFromEmptyContext ≡ false

canonicalWette1969RecursiveDefinitionSpineBoundary :
  Wette1969RecursiveDefinitionSpineBoundary
canonicalWette1969RecursiveDefinitionSpineBoundary =
  wette1969RecursiveDefinitionSpineBoundary
    true refl true refl true refl false refl
