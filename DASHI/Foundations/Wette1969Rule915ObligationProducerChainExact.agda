module DASHI.Foundations.Wette1969Rule915ObligationProducerChainExact where

------------------------------------------------------------------------
-- PROOF-CARRYING PRODUCER CHAIN FOR THE TWO 9.1.5 L-OBLIGATION SUBGRAPHS
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969Rule915PredicateProducerExact as Rule915
import DASHI.Foundations.Wette1969Rule915ObligationSubgraphsExact as Obligations
import DASHI.Foundations.Wette1969Rule915CertifiedObligationApplicationExact as Certified915
import DASHI.Foundations.Wette1969ProofCarryingRuleApplicationExact as Historical
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite
import DASHI.Foundations.Wette1969DerivationClosureExact as Closure

WordTerm = Signature.WordTerm
Context = Finite.DerivationContext

historicalSystem = Closure.historicalApplicationSystem

------------------------------------------------------------------------
-- Evidence transport helpers.  These are intentionally componentwise: the
-- source says premises 10--15 are shared by both major obligations, and this
-- transport preserves one shared proof object rather than copying a branch.
------------------------------------------------------------------------

transportFirstSeven :
  {context : Context} →
  {transcription : Rule915.Rule915PremiseTranscription} →
  (trace : PCRA.CertifiedRuleTrace historicalSystem context) →
  Obligations.FirstSevenEvidence context transcription →
  Obligations.FirstSevenEvidence
    (PCRA.runCertifiedTrace historicalSystem trace) transcription
transportFirstSeven trace evidence =
  Obligations.firstSevenEvidence
    (Closure.certifiedTracePreservesPriorFormula trace _ (Obligations.e01 evidence))
    (Closure.certifiedTracePreservesPriorFormula trace _ (Obligations.e02 evidence))
    (Closure.certifiedTracePreservesPriorFormula trace _ (Obligations.e03 evidence))
    (Closure.certifiedTracePreservesPriorFormula trace _ (Obligations.e04 evidence))
    (Closure.certifiedTracePreservesPriorFormula trace _ (Obligations.e05 evidence))
    (Closure.certifiedTracePreservesPriorFormula trace _ (Obligations.e06 evidence))
    (Closure.certifiedTracePreservesPriorFormula trace _ (Obligations.e07 evidence))

transportShared1015 :
  {context : Context} →
  {transcription : Rule915.Rule915PremiseTranscription} →
  (trace : PCRA.CertifiedRuleTrace historicalSystem context) →
  Obligations.Shared1015Evidence context transcription →
  Obligations.Shared1015Evidence
    (PCRA.runCertifiedTrace historicalSystem trace) transcription
transportShared1015 trace evidence =
  Obligations.shared1015Evidence
    (Closure.certifiedTracePreservesPriorFormula trace _ (Obligations.e10 evidence))
    (Closure.certifiedTracePreservesPriorFormula trace _ (Obligations.e11 evidence))
    (Closure.certifiedTracePreservesPriorFormula trace _ (Obligations.e12 evidence))
    (Closure.certifiedTracePreservesPriorFormula trace _ (Obligations.e13 evidence))
    (Closure.certifiedTracePreservesPriorFormula trace _ (Obligations.e14 evidence))
    (Closure.certifiedTracePreservesPriorFormula trace _ (Obligations.e15 evidence))

------------------------------------------------------------------------
-- Producer chain:
--   initial --sharedTrace--> shared target
--           --inductionTrace--> induction target
--           --independenceTrace--> common final target.
--
-- Each branch carries evidence at the state where it was actually produced.
-- Monotone closure transports the earlier branch and the shared core to the
-- final target before 9.1.5 is certified.
------------------------------------------------------------------------

record Rule915ObligationProducerChain
    (initial : Context)
    (transcription : Rule915.Rule915PremiseTranscription) : Set₁ where
  constructor rule915ObligationProducerChain
  field
    firstSevenAtInitial : Obligations.FirstSevenEvidence initial transcription

    sharedTrace : PCRA.CertifiedRuleTrace historicalSystem initial
    sharedProduced :
      Obligations.Shared1015Evidence
        (PCRA.runCertifiedTrace historicalSystem sharedTrace)
        transcription

    inductionTrace :
      PCRA.CertifiedRuleTrace historicalSystem
        (PCRA.runCertifiedTrace historicalSystem sharedTrace)

    inductionProduced :
      let sharedAtInduction = transportShared1015 inductionTrace sharedProduced
      in Obligations.PredecessorInductionBranch
           (PCRA.runCertifiedTrace historicalSystem inductionTrace)
           transcription
           sharedAtInduction

    independenceTrace :
      PCRA.CertifiedRuleTrace historicalSystem
        (PCRA.runCertifiedTrace historicalSystem inductionTrace)

    independenceProduced :
      let sharedAtInduction = transportShared1015 inductionTrace sharedProduced
          sharedAtFinal = transportShared1015 independenceTrace sharedAtInduction
      in Obligations.DefiniensIndependenceBranch
           (PCRA.runCertifiedTrace historicalSystem independenceTrace)
           transcription
           sharedAtFinal

open Rule915ObligationProducerChain public

obligationTarget :
  {initial : Context} →
  {transcription : Rule915.Rule915PremiseTranscription} →
  Rule915ObligationProducerChain initial transcription → Context
obligationTarget chain =
  PCRA.runCertifiedTrace historicalSystem (independenceTrace chain)

firstSevenAtTarget :
  {initial : Context} →
  {transcription : Rule915.Rule915PremiseTranscription} →
  (chain : Rule915ObligationProducerChain initial transcription) →
  Obligations.FirstSevenEvidence (obligationTarget chain) transcription
firstSevenAtTarget chain =
  transportFirstSeven
    (independenceTrace chain)
    (transportFirstSeven
      (inductionTrace chain)
      (transportFirstSeven
        (sharedTrace chain)
        (firstSevenAtInitial chain)))

sharedAtTarget :
  {initial : Context} →
  {transcription : Rule915.Rule915PremiseTranscription} →
  (chain : Rule915ObligationProducerChain initial transcription) →
  Obligations.Shared1015Evidence (obligationTarget chain) transcription
sharedAtTarget chain =
  transportShared1015
    (independenceTrace chain)
    (transportShared1015
      (inductionTrace chain)
      (sharedProduced chain))

transportInductionBranch :
  {context : Context} →
  {transcription : Rule915.Rule915PremiseTranscription} →
  {shared : Obligations.Shared1015Evidence context transcription} →
  (trace : PCRA.CertifiedRuleTrace historicalSystem context) →
  Obligations.PredecessorInductionBranch context transcription shared →
  Obligations.PredecessorInductionBranch
    (PCRA.runCertifiedTrace historicalSystem trace)
    transcription
    (transportShared1015 trace shared)
transportInductionBranch trace branch =
  Obligations.predecessorInductionBranch
    (Closure.certifiedTracePreservesPriorFormula trace _ (Obligations.e08 branch))
    (Closure.certifiedTracePreservesPriorFormula trace _ (Obligations.e09 branch))
    (Closure.certifiedTracePreservesPriorFormula trace _ (Obligations.e16 branch))
    (Closure.certifiedTracePreservesPriorFormula trace _ (Obligations.e17 branch))
    (Closure.certifiedTracePreservesPriorFormula trace _ (Obligations.e18 branch))

obligationEvidenceAtTarget :
  {initial : Context} →
  {transcription : Rule915.Rule915PremiseTranscription} →
  (chain : Rule915ObligationProducerChain initial transcription) →
  Obligations.Rule915ObligationEvidence (obligationTarget chain) transcription
obligationEvidenceAtTarget chain =
  Obligations.rule915ObligationEvidence
    (firstSevenAtTarget chain)
    (sharedAtTarget chain)
    (transportInductionBranch
      (independenceTrace chain)
      (inductionProduced chain))
    (independenceProduced chain)

selectRule915AtObligationTarget :
  {initial : Context} →
  {transcription : Rule915.Rule915PremiseTranscription} →
  (arity recursivePredicate : WordTerm) →
  (chain : Rule915ObligationProducerChain initial transcription) →
  PCRA.SelectedRuleApplication historicalSystem (obligationTarget chain)
selectRule915AtObligationTarget arity recursivePredicate chain =
  Certified915.selectRule915FromObligationEvidence
    (obligationTarget chain)
    _ arity recursivePredicate
    (obligationEvidenceAtTarget chain)

completeObligationThen915Trace :
  {initial : Context} →
  {transcription : Rule915.Rule915PremiseTranscription} →
  (arity recursivePredicate : WordTerm) →
  (chain : Rule915ObligationProducerChain initial transcription) →
  PCRA.CertifiedRuleTrace historicalSystem initial
completeObligationThen915Trace arity recursivePredicate chain =
  PCRA.appendCertifiedTrace
    (sharedTrace chain)
    (PCRA.appendCertifiedTrace
      (inductionTrace chain)
      (PCRA.appendCertifiedTrace
        (independenceTrace chain)
        (PCRA.choose
          (selectRule915AtObligationTarget arity recursivePredicate chain)
          PCRA.done)))

record Wette1969Rule915ObligationProducerChainBoundary : Set where
  constructor wette1969Rule915ObligationProducerChainBoundary
  field
    shared1015ProducedOnceAndTransportedToBothBranches : Bool
    shared1015ProducedOnceAndTransportedToBothBranchesIsTrue :
      shared1015ProducedOnceAndTransportedToBothBranches ≡ true
    inductionAndIndependenceEvidenceMeetAtOneActualTarget : Bool
    inductionAndIndependenceEvidenceMeetAtOneActualTargetIsTrue :
      inductionAndIndependenceEvidenceMeetAtOneActualTarget ≡ true
    completeObligationProducerChainCanCertifyRule915 : Bool
    completeObligationProducerChainCanCertifyRule915IsTrue :
      completeObligationProducerChainCanCertifyRule915 ≡ true
    producerChainAutomaticallyConstructsAllUnderlyingHistoricalRules : Bool
    producerChainAutomaticallyConstructsAllUnderlyingHistoricalRulesIsFalse :
      producerChainAutomaticallyConstructsAllUnderlyingHistoricalRules ≡ false

canonicalWette1969Rule915ObligationProducerChainBoundary :
  Wette1969Rule915ObligationProducerChainBoundary
canonicalWette1969Rule915ObligationProducerChainBoundary =
  wette1969Rule915ObligationProducerChainBoundary
    true refl true refl true refl false refl
