module DASHI.Reasoning.PlatoSymposiumProofSearchExperimentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryFactorisationSufficiency as Query
import DASHI.Law.SensibLawDialecticalProofSearchExact as DialecticalSearch
import DASHI.Reasoning.AristotleExperimentalProofSearchExact as ExperimentalSearch
import DASHI.Reasoning.AristotleMergeExperimentDesignExact as ExperimentDesign
import DASHI.Philosophy.PlatoSymposiumPhilosophyBridgeExact as Plato

------------------------------------------------------------------------
-- PLATO SYMPOSIUM x PROOF SEARCH / EXPERIMENT DESIGN
------------------------------------------------------------------------

existingProofSearchOwnersReused : Bool
existingProofSearchOwnersReused = true

existingDialecticalSearchBoundary : DialecticalSearch.DialecticalSearchBoundary
existingDialecticalSearchBoundary = DialecticalSearch.canonicalDialecticalSearchBoundary

existingExperimentalSearchBoundary : ExperimentalSearch.AristotleExperimentalProofSearchBoundary
existingExperimentalSearchBoundary = ExperimentalSearch.canonicalAristotleExperimentalProofSearchBoundary

existingMergeExperimentBoundary : ExperimentDesign.AristotleMergeExperimentBoundary
existingMergeExperimentBoundary = ExperimentDesign.canonicalAristotleMergeExperimentBoundary

pluralSpeechSourceContract : Plato.LeanPhilosophyTheoremContract
pluralSpeechSourceContract = Plato.pluralSpeechConflictContract

rightOpinionSourceContract : Plato.LeanPhilosophyTheoremContract
rightOpinionSourceContract = Plato.rightOpinionContract

------------------------------------------------------------------------
-- 1. Same current utterance, different retained history -> different next probe.
------------------------------------------------------------------------

data DialogueHistoryWorld : Set where
  sameClaimWithLiveContradiction : DialogueHistoryWorld
  sameClaimWithUnresolvedLineage : DialogueHistoryWorld

data CurrentUtteranceSurface : Set where
  sameCurrentClaim : CurrentUtteranceSurface

data NextProbeQuery : Set where
  nextUsefulProbeQuestion : NextProbeQuery

data NextProbeAnswer : Set where
  contradictionDiscriminator : NextProbeAnswer
  provenanceDiscriminator : NextProbeAnswer

currentUtteranceProjection : DialogueHistoryWorld → CurrentUtteranceSurface
currentUtteranceProjection sameClaimWithLiveContradiction = sameCurrentClaim
currentUtteranceProjection sameClaimWithUnresolvedLineage = sameCurrentClaim

NextProbeAnswerFor : NextProbeQuery → Set
NextProbeAnswerFor nextUsefulProbeQuestion = NextProbeAnswer

askNextProbe : (query : NextProbeQuery) → DialogueHistoryWorld → NextProbeAnswerFor query
askNextProbe nextUsefulProbeQuestion sameClaimWithLiveContradiction = contradictionDiscriminator
askNextProbe nextUsefulProbeQuestion sameClaimWithUnresolvedLineage = provenanceDiscriminator

nextProbeQuestions : Query.InquiryQuestionFamily DialogueHistoryWorld NextProbeQuery
nextProbeQuestions = Query.inquiryQuestionFamily NextProbeAnswerFor askNextProbe

currentUtteranceDoesNotDetermineNextProbe :
  Query.FactorsThrough nextProbeQuestions currentUtteranceProjection nextUsefulProbeQuestion → ⊥
currentUtteranceDoesNotDetermineNextProbe factor = helper first second
  where
    first : contradictionDiscriminator ≡ Query.quotientAnswer factor sameCurrentClaim
    first = Query.factorisation factor sameClaimWithLiveContradiction
    second : provenanceDiscriminator ≡ Query.quotientAnswer factor sameCurrentClaim
    second = Query.factorisation factor sameClaimWithUnresolvedLineage
    helper :
      contradictionDiscriminator ≡ Query.quotientAnswer factor sameCurrentClaim →
      provenanceDiscriminator ≡ Query.quotientAnswer factor sameCurrentClaim → ⊥
    helper refl ()

------------------------------------------------------------------------
-- 2. Number of supporting strands is not the inquiry state.
------------------------------------------------------------------------

data SupportWorld : Set where
  twoSupportsWithOpenDefeater : SupportWorld
  twoSupportsWithResolvedDiscriminator : SupportWorld

data SupportCountSurface : Set where
  twoSupports : SupportCountSurface

data InquiryStateQuery : Set where
  inquiryStateQuestion : InquiryStateQuery

data InquiryStateAnswer : Set where
  defeaterSearchStillRequired : InquiryStateAnswer
  consumerDiscriminatorResolved : InquiryStateAnswer

supportCountProjection : SupportWorld → SupportCountSurface
supportCountProjection twoSupportsWithOpenDefeater = twoSupports
supportCountProjection twoSupportsWithResolvedDiscriminator = twoSupports

InquiryStateAnswerFor : InquiryStateQuery → Set
InquiryStateAnswerFor inquiryStateQuestion = InquiryStateAnswer

askInquiryState : (query : InquiryStateQuery) → SupportWorld → InquiryStateAnswerFor query
askInquiryState inquiryStateQuestion twoSupportsWithOpenDefeater = defeaterSearchStillRequired
askInquiryState inquiryStateQuestion twoSupportsWithResolvedDiscriminator = consumerDiscriminatorResolved

inquiryStateQuestions : Query.InquiryQuestionFamily SupportWorld InquiryStateQuery
inquiryStateQuestions = Query.inquiryQuestionFamily InquiryStateAnswerFor askInquiryState

supportCountDoesNotDetermineInquiryState :
  Query.FactorsThrough inquiryStateQuestions supportCountProjection inquiryStateQuestion → ⊥
supportCountDoesNotDetermineInquiryState factor = helper first second
  where
    first : defeaterSearchStillRequired ≡ Query.quotientAnswer factor twoSupports
    first = Query.factorisation factor twoSupportsWithOpenDefeater
    second : consumerDiscriminatorResolved ≡ Query.quotientAnswer factor twoSupports
    second = Query.factorisation factor twoSupportsWithResolvedDiscriminator
    helper :
      defeaterSearchStillRequired ≡ Query.quotientAnswer factor twoSupports →
      consumerDiscriminatorResolved ≡ Query.quotientAnswer factor twoSupports → ⊥
    helper refl ()

------------------------------------------------------------------------
-- 3. Consensus status is too coarse for a declared downstream consumer.
------------------------------------------------------------------------

data ConsensusWorld : Set where
  noConsensusButConsumerResolved : ConsensusWorld
  noConsensusAndConsumerOpen : ConsensusWorld

data ConsensusStatusSurface : Set where
  noConsensusSurface : ConsensusStatusSurface

data ConsumerResolutionQuery : Set where
  consumerResolutionQuestion : ConsumerResolutionQuery

data ConsumerResolutionAnswer : Set where
  sufficientForDeclaredConsumer : ConsumerResolutionAnswer
  insufficientForDeclaredConsumer : ConsumerResolutionAnswer

consensusStatusProjection : ConsensusWorld → ConsensusStatusSurface
consensusStatusProjection noConsensusButConsumerResolved = noConsensusSurface
consensusStatusProjection noConsensusAndConsumerOpen = noConsensusSurface

ConsumerResolutionAnswerFor : ConsumerResolutionQuery → Set
ConsumerResolutionAnswerFor consumerResolutionQuestion = ConsumerResolutionAnswer

askConsumerResolution :
  (query : ConsumerResolutionQuery) → ConsensusWorld → ConsumerResolutionAnswerFor query
askConsumerResolution consumerResolutionQuestion noConsensusButConsumerResolved = sufficientForDeclaredConsumer
askConsumerResolution consumerResolutionQuestion noConsensusAndConsumerOpen = insufficientForDeclaredConsumer

consumerResolutionQuestions : Query.InquiryQuestionFamily ConsensusWorld ConsumerResolutionQuery
consumerResolutionQuestions = Query.inquiryQuestionFamily ConsumerResolutionAnswerFor askConsumerResolution

consensusDoesNotDetermineConsumerResolution :
  Query.FactorsThrough consumerResolutionQuestions consensusStatusProjection consumerResolutionQuestion → ⊥
consensusDoesNotDetermineConsumerResolution factor = helper first second
  where
    first : sufficientForDeclaredConsumer ≡ Query.quotientAnswer factor noConsensusSurface
    first = Query.factorisation factor noConsensusButConsumerResolved
    second : insufficientForDeclaredConsumer ≡ Query.quotientAnswer factor noConsensusSurface
    second = Query.factorisation factor noConsensusAndConsumerOpen
    helper :
      sufficientForDeclaredConsumer ≡ Query.quotientAnswer factor noConsensusSurface →
      insufficientForDeclaredConsumer ≡ Query.quotientAnswer factor noConsensusSurface → ⊥
    helper refl ()

------------------------------------------------------------------------
-- Existing search boundaries pinned rather than redefined.
------------------------------------------------------------------------

supportDoesNotCreateTruth : DialecticalSearch.RetrievedSupportMeansTruth → ⊥
supportDoesNotCreateTruth = DialecticalSearch.supportDoesNotMeanTruth

moreSupportDoesNotReplaceDefeaterSearch : DialecticalSearch.MoreSupportMayReplaceDefeaterSearch → ⊥
moreSupportDoesNotReplaceDefeaterSearch = DialecticalSearch.supportDoesNotReplaceDefeaterSearch

searchPolicyDoesNotReplaceProofValidity :
  ExperimentalSearch.searchPolicyReplacesProofValiditySemantics
    ExperimentalSearch.canonicalAristotleExperimentalProofSearchBoundary ≡ false
searchPolicyDoesNotReplaceProofValidity = refl

nextExperimentMayDependOnOutcome :
  ExperimentalSearch.nextProofExperimentMayDependOnObservedOutcome
    ExperimentalSearch.canonicalAristotleExperimentalProofSearchBoundary ≡ true
nextExperimentMayDependOnOutcome = refl

provenanceMayBeSecondStageDiscriminator :
  ExperimentDesign.provenanceCanBeASecondStageDiscriminator
    ExperimentDesign.canonicalAristotleMergeExperimentBoundary ≡ true
provenanceMayBeSecondStageDiscriminator = refl

record PlatoSymposiumProofSearchBoundary : Set where
  constructor plato-symposium-proof-search-boundary
  field
    symposiumDialogueIsProofSearchAlgorithm : Bool
    supportCountCreatesTruth : Bool
    consensusClosesEveryConsumer : Bool
    currentUtteranceAloneDeterminesNextProbe : Bool
    proofSearchMayUseSupportDefeaterComparatorRoles : Bool
    nextProbeMayDependOnRetainedHistory : Bool
    sequentialExperimentMayDependOnPriorOutcome : Bool
    proofValidityRemainsSeparatelyOwned : Bool

open PlatoSymposiumProofSearchBoundary public

canonicalPlatoSymposiumProofSearchBoundary : PlatoSymposiumProofSearchBoundary
canonicalPlatoSymposiumProofSearchBoundary =
  plato-symposium-proof-search-boundary false false false false true true true true

------------------------------------------------------------------------
-- Compatibility surface for the dedicated concurrent regression owner.
------------------------------------------------------------------------

canonicalPlatoProofSearchExperimentBoundary : PlatoSymposiumProofSearchBoundary
canonicalPlatoProofSearchExperimentBoundary = canonicalPlatoSymposiumProofSearchBoundary

currentUtteranceDeterminesNextProbe : PlatoSymposiumProofSearchBoundary → Bool
currentUtteranceDeterminesNextProbe = currentUtteranceAloneDeterminesNextProbe

supportCountDeterminesInquiryState : PlatoSymposiumProofSearchBoundary → Bool
supportCountDeterminesInquiryState _ = false

consensusDeterminesConsumerRelevantResolution : PlatoSymposiumProofSearchBoundary → Bool
consensusDeterminesConsumerRelevantResolution = consensusClosesEveryConsumer

nextQuestionMayDependOnObservedOutcome : PlatoSymposiumProofSearchBoundary → Bool
nextQuestionMayDependOnObservedOutcome = sequentialExperimentMayDependOnPriorOutcome

searchStrategyCreatesProofValidity : PlatoSymposiumProofSearchBoundary → Bool
searchStrategyCreatesProofValidity _ = false

proofSearchSummary : String
proofSearchSummary =
  "The Symposium is used only as a source-bounded fixture for plural, history-sensitive inquiry. DASHI's existing search/experiment machinery owns support-defeater-comparator roles, consumer-relevant discriminators and outcome-adaptive probe selection; current utterance, support count and consensus status are each too coarse to determine the relevant downstream inquiry state."
