module DASHI.Cognition.PNF.SensibLawCountryCommunityPaymentAcquisitionPlanV02Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawCountryCommunityOutcomeAuthorityPaymentCutV02Exact as Cut
import DASHI.Cognition.PNF.SensibLawCountryRealisedRepairProofSearchBridgeV02Exact as Bridge
import DASHI.Law.SensibLawProviderNeutralLegalQueryAlgebraExact as Query
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search
import DASHI.Law.SensibLawCorpusProducerRoutingExact as Routing

------------------------------------------------------------------------
-- PAYMENT CUT -> BOUNDED ACQUISITION FAMILY
--
-- The first genuine residual is no longer a prose TODO.  It is decomposed into
-- exact search hypotheses for a selected consumer.  Candidate discovery,
-- consumer/outcome correspondence, mandate scope and current validity remain
-- separate; no lexical hit or provider result pays the cut by existence.
------------------------------------------------------------------------

data PaymentCoordinate : Set where
  communityOutcomeStatementCoordinate
  consumerOutcomeCorrespondenceCoordinate
  communityMandateScopeCoordinate
  mandateTemporalValidityCoordinate
  authorityRoleCorrespondenceCoordinate
  : PaymentCoordinate

producerForPaymentCoordinate : PaymentCoordinate → Search.ProducerClass
producerForPaymentCoordinate communityOutcomeStatementCoordinate = Search.propositionSourceProducer
producerForPaymentCoordinate consumerOutcomeCorrespondenceCoordinate = Search.applicabilityProducer
producerForPaymentCoordinate communityMandateScopeCoordinate = Search.attributionProducer
producerForPaymentCoordinate mandateTemporalValidityCoordinate = Search.temporalProducer
producerForPaymentCoordinate authorityRoleCorrespondenceCoordinate = Search.attributionProducer

firstMissingPaymentCoordinate : PaymentCoordinate
firstMissingPaymentCoordinate = communityOutcomeStatementCoordinate

firstMissingProducerExact :
  producerForPaymentCoordinate firstMissingPaymentCoordinate
  ≡ Search.propositionSourceProducer
firstMissingProducerExact = refl

------------------------------------------------------------------------
-- Provider-neutral queries.  These are shapes for the local compiled world
-- corpus first; provider lowering remains downstream.
------------------------------------------------------------------------

outcomeStatementQuery : Query.QueryExpr
outcomeStatementQuery = Query.orQ
  (Query.phraseQ "community-defined outcome")
  (Query.orQ
    (Query.phraseQ "Traditional Owners seek")
    (Query.orQ
      (Query.phraseQ "Cultural Custodians seek")
      (Query.phraseQ "First Nations delegates call for")))

consumerCorrespondenceQuery : Query.QueryExpr
consumerCorrespondenceQuery = Query.andQ
  (Query.phraseQ "declared consumer")
  (Query.orQ
    (Query.phraseQ "same outcome")
    (Query.phraseQ "satisfactory outcome"))

mandateScopeQuery : Query.QueryExpr
mandateScopeQuery = Query.orQ
  (Query.phraseQ "authorised by")
  (Query.orQ
    (Query.phraseQ "mandate to represent")
    (Query.phraseQ "decision-making authority"))

mandateTemporalQuery : Query.QueryExpr
mandateTemporalQuery = Query.orQ
  (Query.phraseQ "current mandate")
  (Query.orQ
    (Query.phraseQ "current representative")
    (Query.phraseQ "authorised representative"))

authorityRoleQuery : Query.QueryExpr
authorityRoleQuery = Query.orQ
  (Query.phraseQ "Traditional Owner community")
  (Query.orQ
    (Query.phraseQ "registered native title body corporate")
    (Query.phraseQ "common law holders"))

------------------------------------------------------------------------
-- One bounded hypothesis family for the current first residual.
------------------------------------------------------------------------

currentOutcomeIntent : Search.SearchIntent
currentOutcomeIntent = Bridge.searchIntentFor Bridge.affectedCommunityOutcomeResidualV02

primaryOutcomeHypothesis : Query.SearchHypothesis
primaryOutcomeHypothesis = Query.searchHypothesis
  currentOutcomeIntent
  "community-originating statement defines a satisfactory outcome for the selected consumer"
  "source-attributed community proposition naming the desired material/governance outcome and the affected consumer"
  Query.vocabularyExplorationProbe
  outcomeStatementQuery
  "CommunityOutcomePaymentEvidence.candidateActuallyDefinesSatisfactoryOutcomeForConsumer"
  "exclude State-authored proxies, secondary paraphrase without originating carrier, and generic Indigenous-policy slogans"

consumerCorrespondenceHypothesis : Query.SearchHypothesis
consumerCorrespondenceHypothesis = Query.searchHypothesis
  currentOutcomeIntent
  "candidate proposition is actually about the declared consumer"
  "same community/Country/problem relation between source proposition and operational consumer"
  Query.supportingProbe
  consumerCorrespondenceQuery
  "CommunityOutcomePaymentEvidence.propositionCorrespondsToDeclaredConsumer"
  "exclude neighbouring communities, generic national claims and merely analogous Country disputes"

mandateScopeHypothesis : Query.SearchHypothesis
mandateScopeHypothesis = Query.searchHypothesis
  (Bridge.searchIntentFor Bridge.communityAuthorityCapacityResidualV02)
  "identified speaker/body has mandate within the relevant authority role"
  "source-attributed mandate/decision process establishing scope for the selected outcome"
  Query.authorityFamilyExplorationProbe
  mandateScopeQuery
  "AuthorityAdmissionEvidence.mandateWithinRoleScope"
  "exclude statutory corporate role as automatic whole-community authority and provenance as automatic mandate"

mandateTemporalHypothesis : Query.SearchHypothesis
mandateTemporalHypothesis = Query.searchHypothesis
  (Bridge.searchIntentFor Bridge.communityAuthorityCapacityResidualV02)
  "mandate remains current for the selected consumer/outcome"
  "dated source establishing present or explicitly bounded temporal authority"
  Query.supportingProbe
  mandateTemporalQuery
  "AuthorityAdmissionEvidence.mandateCurrentlyValid"
  "exclude historical mandate carried forward without temporal evidence"

authorityRoleHypothesis : Query.SearchHypothesis
authorityRoleHypothesis = Query.searchHypothesis
  (Bridge.searchIntentFor Bridge.communityAuthorityCapacityResidualV02)
  "authority role corresponds to the consumer rather than merely a legal carrier"
  "Traditional Owner/community/common-law-holder/PBC/RNTBC role identified without collapsing them"
  Query.supportingProbe
  authorityRoleQuery
  "JointOutcomeAuthorityPaymentV02.sameConsumerAcrossOutcomeAndAuthority"
  "exclude RNTBC=PBC=TraditionalOwnerCommunity and statutory representation=sovereignty promotions"

currentCommunityPaymentSearchFamily : Query.SearchHypothesisFamily
currentCommunityPaymentSearchFamily = Query.searchHypothesisFamily
  currentOutcomeIntent
  primaryOutcomeHypothesis
  (consumerCorrespondenceHypothesis ∷ mandateScopeHypothesis ∷ mandateTemporalHypothesis ∷ authorityRoleHypothesis ∷ [])
  []
  []
  "country-community-outcome-authority/payment-cut/search-family/v02"

------------------------------------------------------------------------
-- Existing corpus routing says the first pass can stay inside the compiled
-- world/matter/testimony surfaces rather than widening to generic web search.
------------------------------------------------------------------------

firstResidualEligibleCorpora : List Routing.CorpusClass
firstResidualEligibleCorpora = Routing.eligibleCorpora Search.propositionSourceProducer

firstEligibleCorpusIsLocalWorld :
  firstResidualEligibleCorpora
  ≡ (Routing.localCompiledWorldCorpus ∷ Routing.officialCaseLawCorpus ∷ Routing.officialLegislationCorpus ∷ Routing.transcriptAndTestimonyCorpus ∷ Routing.matterDocumentCorpus ∷ [])
firstEligibleCorpusIsLocalWorld = refl

------------------------------------------------------------------------
-- Fail-closed execution boundary.
------------------------------------------------------------------------

data QueryHitPaysCommunityOutcome : Set where
data QueryHitPaysCommunityMandate : Set where
data SameNameMeansSameCommunityConsumer : Set where
data LitigationPartyMeansWholeCommunityMandate : Set where

queryHitDoesNotPayOutcome : QueryHitPaysCommunityOutcome → ⊥
queryHitDoesNotPayOutcome ()

queryHitDoesNotPayMandate : QueryHitPaysCommunityMandate → ⊥
queryHitDoesNotPayMandate ()

sameNameDoesNotEstablishConsumerIdentity : SameNameMeansSameCommunityConsumer → ⊥
sameNameDoesNotEstablishConsumerIdentity ()

litigationPartyDoesNotCreateWholeCommunityMandate :
  LitigationPartyMeansWholeCommunityMandate → ⊥
litigationPartyDoesNotCreateWholeCommunityMandate ()

record PaymentAcquisitionBoundary : Set where
  constructor payment-acquisition-boundary
  field
    paymentCutHasExecutableSearchFamily : Bool
    paymentCutHasExecutableSearchFamilyIsTrue : paymentCutHasExecutableSearchFamily ≡ true
    firstPassMayUseLocalCompiledWorld : Bool
    firstPassMayUseLocalCompiledWorldIsTrue : firstPassMayUseLocalCompiledWorld ≡ true
    resultExistencePaysPayment : Bool
    resultExistencePaysPaymentIsFalse : resultExistencePaysPayment ≡ false
    authoritySearchMayCollapseRoles : Bool
    authoritySearchMayCollapseRolesIsFalse : authoritySearchMayCollapseRoles ≡ false

canonicalPaymentAcquisitionBoundary : PaymentAcquisitionBoundary
canonicalPaymentAcquisitionBoundary = payment-acquisition-boundary
  true refl
  true refl
  false refl
  false refl

paymentCutStillRequiresConsumerMatch :
  Cut.communityOutcomeConsumerMatchIsStillRequired ≡ true
paymentCutStillRequiresConsumerMatch = refl

paymentCutStillRequiresCurrentMandate :
  Cut.currentCommunityMandateIsStillRequired ≡ true
paymentCutStillRequiresCurrentMandate = refl
