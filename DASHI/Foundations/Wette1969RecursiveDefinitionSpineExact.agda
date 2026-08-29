module DASHI.Foundations.Wette1969RecursiveDefinitionSpineExact where

------------------------------------------------------------------------
-- END-TO-END LOCAL RECURSIVE-DEFINITION SPINE
--
-- Factored 9.1.5 obligation producers -> certified 9.1.5 -> tuple/freshness
-- producer traces -> certified two-stage II -> 8.2.8 -> 9.3.24/25.
--
-- The key weld is an equality receipt identifying the first critical producer
-- trace with the actual obligation-chain-plus-9.1.5 trace.  The tuple and
-- freshness traces remain proof-carrying producers at the states reached from
-- that trace; existing concrete modules instantiate them with 8.3.2 / 8.1.12.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969Rule915PredicateProducerExact as Rule915
import DASHI.Foundations.Wette1969Rule915ObligationProducerChainExact as Obligations
import DASHI.Foundations.Wette1969Rule828To9324x25DerivationExact as Weld
import DASHI.Foundations.Wette1969CriticalPremiseLocalDerivationExact as Local
import DASHI.Foundations.Wette1969CertifiedTwoStageIIDerivationExact as CertifiedII
import DASHI.Foundations.Wette1969DependentTwoStageSubstitutionExact as TwoStage
import DASHI.Foundations.Wette1969FullyGeneratedCriticalApplicationExact as Fully
import DASHI.Foundations.Wette1969Rule9324x25PremiseTemplateExact as CriticalRule
import DASHI.Foundations.Wette1969InitialRuleTranscriptionExact as RuleBody
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite

WordTerm = Signature.WordTerm
Context = Finite.DerivationContext

historicalSystem : PCRA.RuleApplicationSystem Context RuleBody.HistoricalRuleBody
historicalSystem = Local.historicalSystem

obligation915Trace :
  {initial : Context} →
  {transcription : Rule915.Rule915PremiseTranscription} →
  (arity : WordTerm) →
  (stages : TwoStage.DependentTwoStageSubstitution) →
  Obligations.Rule915ObligationProducerChain initial transcription →
  PCRA.CertifiedRuleTrace historicalSystem initial
obligation915Trace arity stages chain =
  Obligations.completeObligationThen915Trace
    arity
    (TwoStage.recursivePredicate (TwoStage.second stages))
    chain

record RecursiveDefinitionSpineInputs
    (initial : Context)
    (transcription : Rule915.Rule915PremiseTranscription)
    (arity freshnessContext : WordTerm)
    (stages : TwoStage.DependentTwoStageSubstitution) : Set₁ where
  constructor recursiveDefinitionSpineInputs
  field
    obligationChain :
      Obligations.Rule915ObligationProducerChain initial transcription

    firstThree :
      Local.FirstThreeCriticalProducerChain
        initial
        (Weld.criticalPremiseParametersFromStages arity freshnessContext stages)

    predicateTraceIsObligation915Trace :
      Local.predicateTrace firstThree
        ≡ obligation915Trace arity stages obligationChain

    sequentialII :
      CertifiedII.CertifiedTwoStageIIDerivation
        (Local.producerTarget firstThree)
        stages

open RecursiveDefinitionSpineInputs public

fullyGenerated :
  {initial : Context} →
  {transcription : Rule915.Rule915PremiseTranscription} →
  {arity freshnessContext : WordTerm} →
  {stages : TwoStage.DependentTwoStageSubstitution} →
  RecursiveDefinitionSpineInputs initial transcription arity freshnessContext stages →
  Fully.FullyGeneratedCriticalPremises initial arity freshnessContext stages
fullyGenerated inputs =
  Fully.fullyGeneratedCriticalPremises
    (firstThree inputs)
    (sequentialII inputs)

recursiveDefinitionTrace9324 :
  {initial : Context} →
  {transcription : Rule915.Rule915PremiseTranscription} →
  {arity freshnessContext : WordTerm} →
  {stages : TwoStage.DependentTwoStageSubstitution} →
  RecursiveDefinitionSpineInputs initial transcription arity freshnessContext stages →
  CriticalRule.Rule9324x25ConclusionParameters →
  PCRA.CertifiedRuleTrace historicalSystem initial
recursiveDefinitionTrace9324 inputs conclusions =
  Fully.fullyGeneratedTrace9324 (fullyGenerated inputs) conclusions

recursiveDefinitionTrace9325 :
  {initial : Context} →
  {transcription : Rule915.Rule915PremiseTranscription} →
  {arity freshnessContext : WordTerm} →
  {stages : TwoStage.DependentTwoStageSubstitution} →
  RecursiveDefinitionSpineInputs initial transcription arity freshnessContext stages →
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
    recursiveSpineKeepsExplicitTraceIdentityReceipt : Bool
    recursiveSpineKeepsExplicitTraceIdentityReceiptIsTrue :
      recursiveSpineKeepsExplicitTraceIdentityReceipt ≡ true
    recursiveSpineIsAlreadyClosedFromEmptyContext : Bool
    recursiveSpineIsAlreadyClosedFromEmptyContextIsFalse :
      recursiveSpineIsAlreadyClosedFromEmptyContext ≡ false

canonicalWette1969RecursiveDefinitionSpineBoundary :
  Wette1969RecursiveDefinitionSpineBoundary
canonicalWette1969RecursiveDefinitionSpineBoundary =
  wette1969RecursiveDefinitionSpineBoundary
    true refl true refl true refl true refl false refl
