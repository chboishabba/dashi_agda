module DASHI.Cognition.PNF.SensibLawCountryRealisedRepairProofSearchBridgeV02Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawCountryRealisedRepairCalibrationV02Exact as Repair
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search
import DASHI.Law.SensibLawProofSearchResultAssessmentExact as Assessment

------------------------------------------------------------------------
-- COUNTRY REALISED-REPAIR V02 -> PROOF-DIRECTED SEARCH
--
-- V02 has materially improved the source atlas, but mapped/partial/negative
-- pressure states are not operational closure.  This bridge turns those live
-- consumer-relative gaps into the existing proof-search ABI without allowing
-- provider choice, State proxies or legal-authority categories to redefine the
-- missing community/realisation coordinate.
------------------------------------------------------------------------

data CountryV02Residual : Set where
  affectedCommunityOutcomeResidualV02
  communityAuthorityCapacityResidualV02
  landCountryControlResidualV02
  independentCorrectionResidualV02
  recurrencePreventionResidualV02
  socioEconomicOutcomeResidualV02
  billyCaseSpecificOddsResidualV02
  : CountryV02Residual

data CountryV02SourceRole : Set where
  communityOriginatingOutcomeSource
  communityAuthorityAndCapacitySource
  landCountryRealisedControlSource
  independentCorrectionObservationSource
  longitudinalRecurrenceObservationSource
  realisedSocioEconomicOutcomeSource
  caseSpecificComplianceCalibrationSource
  : CountryV02SourceRole

producerFor : CountryV02Residual → Search.ProducerClass
producerFor affectedCommunityOutcomeResidualV02 = Search.propositionSourceProducer
producerFor communityAuthorityCapacityResidualV02 = Search.attributionProducer
producerFor landCountryControlResidualV02 = Search.empiricalEvidenceProducer
producerFor independentCorrectionResidualV02 = Search.empiricalEvidenceProducer
producerFor recurrencePreventionResidualV02 = Search.empiricalEvidenceProducer
producerFor socioEconomicOutcomeResidualV02 = Search.empiricalEvidenceProducer
producerFor billyCaseSpecificOddsResidualV02 = Search.discriminatorProducer

modeFor : CountryV02Residual → Search.SearchMode
modeFor affectedCommunityOutcomeResidualV02 = Search.exploreVocabulary
modeFor communityAuthorityCapacityResidualV02 = Search.exploreAuthorityFamily
modeFor landCountryControlResidualV02 = Search.exploitKnownResidual
modeFor independentCorrectionResidualV02 = Search.exploitKnownResidual
modeFor recurrencePreventionResidualV02 = Search.exploitKnownResidual
modeFor socioEconomicOutcomeResidualV02 = Search.exploitKnownResidual
modeFor billyCaseSpecificOddsResidualV02 = Search.compareAuthorities

sourceRoleFor : CountryV02Residual → CountryV02SourceRole
sourceRoleFor affectedCommunityOutcomeResidualV02 = communityOriginatingOutcomeSource
sourceRoleFor communityAuthorityCapacityResidualV02 = communityAuthorityAndCapacitySource
sourceRoleFor landCountryControlResidualV02 = landCountryRealisedControlSource
sourceRoleFor independentCorrectionResidualV02 = independentCorrectionObservationSource
sourceRoleFor recurrencePreventionResidualV02 = longitudinalRecurrenceObservationSource
sourceRoleFor socioEconomicOutcomeResidualV02 = realisedSocioEconomicOutcomeSource
sourceRoleFor billyCaseSpecificOddsResidualV02 = caseSpecificComplianceCalibrationSource

------------------------------------------------------------------------
-- Exact current V02 frontier.
------------------------------------------------------------------------

currentFirstResidualV02 : CountryV02Residual
currentFirstResidualV02 = affectedCommunityOutcomeResidualV02

communityOutcomeStatusIsStructuralConstraintMapped :
  Repair.communityDefinedOutcomeAuthorityStatusV02 ≡ Repair.structuralConstraintMapped
communityOutcomeStatusIsStructuralConstraintMapped = refl

communityAuthorityStatusIsStructuralConstraintMapped :
  Repair.communityAuthorityBearingStatusV02 ≡ Repair.structuralConstraintMapped
communityAuthorityStatusIsStructuralConstraintMapped = refl

landCountryControlStatusIsPartial :
  Repair.landCountryControlStatusV02 ≡ Repair.sourceMappedPartial
landCountryControlStatusIsPartial = refl

independentCorrectionStatusIsPartial :
  Repair.independentCorrectionStatusV02 ≡ Repair.sourceMappedPartial
independentCorrectionStatusIsPartial = refl

recurrencePreventionStatusHasNegativePressure :
  Repair.recurrencePreventionStatusV02 ≡ Repair.sourceMappedNegativePressure
recurrencePreventionStatusHasNegativePressure = refl

------------------------------------------------------------------------
-- Search intent lowering.
------------------------------------------------------------------------

searchBudgetFor : CountryV02Residual → Search.SearchBudget
searchBudgetFor affectedCommunityOutcomeResidualV02 = Search.searchBudget 8 32 1 "bounded community-outcome V02 search"
searchBudgetFor communityAuthorityCapacityResidualV02 = Search.searchBudget 8 32 1 "bounded community-authority V02 search"
searchBudgetFor landCountryControlResidualV02 = Search.searchBudget 8 32 1 "bounded land-Country-control V02 search"
searchBudgetFor independentCorrectionResidualV02 = Search.searchBudget 8 32 1 "bounded independent-correction V02 search"
searchBudgetFor recurrencePreventionResidualV02 = Search.searchBudget 8 32 1 "bounded recurrence-prevention V02 search"
searchBudgetFor socioEconomicOutcomeResidualV02 = Search.searchBudget 8 32 1 "bounded socio-economic-outcome V02 search"
searchBudgetFor billyCaseSpecificOddsResidualV02 = Search.searchBudget 8 32 1 "bounded Billy case-specific calibration search"

authorityClassFor : CountryV02Residual → Search.RequiredAuthorityClass
authorityClassFor affectedCommunityOutcomeResidualV02 = Search.primaryTextRequired
authorityClassFor communityAuthorityCapacityResidualV02 = Search.primaryTextRequired
authorityClassFor landCountryControlResidualV02 = Search.supportingSourcePermitted
authorityClassFor independentCorrectionResidualV02 = Search.supportingSourcePermitted
authorityClassFor recurrencePreventionResidualV02 = Search.supportingSourcePermitted
authorityClassFor socioEconomicOutcomeResidualV02 = Search.supportingSourcePermitted
authorityClassFor billyCaseSpecificOddsResidualV02 = Search.supportingSourcePermitted

targetFor : CountryV02Residual → String
targetFor affectedCommunityOutcomeResidualV02 = "affected-community-defined satisfactory outcome for declared consumer"
targetFor communityAuthorityCapacityResidualV02 = "authority-bearing community mandate and practical capacity"
targetFor landCountryControlResidualV02 = "realised land/Country control rather than determination coverage"
targetFor independentCorrectionResidualV02 = "independent correction capable of changing realised operation"
targetFor recurrencePreventionResidualV02 = "longitudinal evidence of recurrence prevention"
targetFor socioEconomicOutcomeResidualV02 = "realised socio-economic outcome for selected consumer"
targetFor billyCaseSpecificOddsResidualV02 = "Billy-specific compliance/remedy calibration distinct from global reference class"

searchIntentFor : CountryV02Residual → Search.SearchIntent
searchIntentFor r = Search.searchIntent
  "Country realised-repair V02 consumer"
  (targetFor r)
  (producerFor r)
  (modeFor r)
  "Australia / relevant Country, community and institutional relation"
  "consumer-relative historical/current envelope"
  (authorityClassFor r)
  "Two-Eyed source braid; source proposition and community authority remain distinct"
  "V02 atlas may seed search but cannot define the missing outcome"
  "same consumer/source-role/authority-domain correspondence required"
  "exclude State proxy substitution; determination-as-control; declaration-as-effect; retrieval-as-payment"
  (searchBudgetFor r)
  "country-realised-repair-v02/proof-search-intent/v1"

currentFirstProducerExact :
  Search.producerClass (searchIntentFor currentFirstResidualV02)
  ≡ Search.propositionSourceProducer
currentFirstProducerExact = refl

currentFirstModeExact :
  Search.mode (searchIntentFor currentFirstResidualV02)
  ≡ Search.exploreVocabulary
currentFirstModeExact = refl

------------------------------------------------------------------------
-- Assessment -> recomputation bridge.
--
-- Candidate acquisition is weaker than payment.  A community-originating
-- proposition can narrow the outcome search while leaving the same outcome
-- residual live.  Only a separately admitted, consumer-matched community
-- outcome may advance the first residual to community authority/capacity.
------------------------------------------------------------------------

data CountryV02RecomputeAction : Set where
  continueBoundedSearch
  recomputeV02Calibration
  reopenV02Coordinate
  retainContestedV02State
  inspectV02Underidentification
  : CountryV02RecomputeAction

recomputeActionFor : Assessment.FrontierChange → CountryV02RecomputeAction
recomputeActionFor Assessment.frontierUnchanged = continueBoundedSearch
recomputeActionFor Assessment.frontierNarrowed = recomputeV02Calibration
recomputeActionFor Assessment.frontierReopened = reopenV02Coordinate
recomputeActionFor Assessment.frontierClosed = recomputeV02Calibration
recomputeActionFor Assessment.frontierContradicted = retainContestedV02State
recomputeActionFor Assessment.frontierUnderidentified = inspectV02Underidentification

communityOutcomeCandidateDeltaV02 : Assessment.SearchFrontierDelta
communityOutcomeCandidateDeltaV02 = Assessment.searchFrontierDelta
  "Country realised-repair V02 consumer"
  "affected-community outcome residual open"
  "community-originating outcome candidate assessed; consumer-specific payment not yet admitted"
  Assessment.frontierNarrowed
  "affectedCommunityOutcomeResidualV02"
  "affectedCommunityOutcomeResidualV02"
  "community-originating candidate with preserved provenance; outcome payment still live"
  "country-realised-repair-v02/community-outcome-candidate-delta/v1"

communityOutcomeCandidateTriggersRecompute :
  recomputeActionFor (Assessment.change communityOutcomeCandidateDeltaV02)
  ≡ recomputeV02Calibration
communityOutcomeCandidateTriggersRecompute = refl

communityOutcomeCandidateKeepsOutcomeResidualLive :
  Assessment.firstResidualAfterReference communityOutcomeCandidateDeltaV02
  ≡ "affectedCommunityOutcomeResidualV02"
communityOutcomeCandidateKeepsOutcomeResidualLive = refl

communityOutcomeAdmittedDeltaV02 : Assessment.SearchFrontierDelta
communityOutcomeAdmittedDeltaV02 = Assessment.searchFrontierDelta
  "Country realised-repair V02 consumer"
  "affected-community outcome residual open"
  "consumer-matched affected-community-defined outcome admitted; authority/capacity remains separate"
  Assessment.frontierClosed
  "affectedCommunityOutcomeResidualV02"
  "communityAuthorityCapacityResidualV02"
  "admitted community-defined outcome receipt with source, consumer and provenance correspondence"
  "country-realised-repair-v02/community-outcome-admitted-delta/v1"

admittedCommunityOutcomeAdvancesToAuthority :
  Assessment.firstResidualAfterReference communityOutcomeAdmittedDeltaV02
  ≡ "communityAuthorityCapacityResidualV02"
admittedCommunityOutcomeAdvancesToAuthority = refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data StructuralConstraintMappedMeansCoordinatePaid : Set where
data StateReviewDefinesAffectedCommunityOutcome : Set where
data CommunityPropositionAutomaticallyCarriesCommunityAuthority : Set where
data CommunityOriginatingCandidatePaysConsumerOutcome : Set where
data DeterminationCoveragePaysLandCountryControl : Set where
data SearchCompletionPaysRealisedRepair : Set where
data FormalFrontierClosureEqualsWorldRepair : Set where

structuralConstraintMappingDoesNotPayCoordinate :
  StructuralConstraintMappedMeansCoordinatePaid → ⊥
structuralConstraintMappingDoesNotPayCoordinate ()

stateReviewDoesNotDefineAffectedCommunityOutcome :
  StateReviewDefinesAffectedCommunityOutcome → ⊥
stateReviewDoesNotDefineAffectedCommunityOutcome ()

communityPropositionDoesNotCreateAuthority :
  CommunityPropositionAutomaticallyCarriesCommunityAuthority → ⊥
communityPropositionDoesNotCreateAuthority ()

communityOriginatingCandidateDoesNotPayConsumerOutcome :
  CommunityOriginatingCandidatePaysConsumerOutcome → ⊥
communityOriginatingCandidateDoesNotPayConsumerOutcome ()

determinationCoverageDoesNotPayControl : DeterminationCoveragePaysLandCountryControl → ⊥
determinationCoverageDoesNotPayControl ()

searchCompletionDoesNotPayRealisedRepair : SearchCompletionPaysRealisedRepair → ⊥
searchCompletionDoesNotPayRealisedRepair ()

formalFrontierClosureDoesNotEqualWorldRepair : FormalFrontierClosureEqualsWorldRepair → ⊥
formalFrontierClosureDoesNotEqualWorldRepair ()

record CountryV02ProofSearchBoundary : Set where
  constructor country-v02-proof-search-boundary
  field
    firstResidualIsCommunityOutcome : Bool
    firstResidualIsCommunityOutcomeIsTrue : firstResidualIsCommunityOutcome ≡ true
    residualPrecedesProviderSelection : Bool
    residualPrecedesProviderSelectionIsTrue : residualPrecedesProviderSelection ≡ true
    communityCandidateMayRemainSameResidual : Bool
    communityCandidateMayRemainSameResidualIsTrue : communityCandidateMayRemainSameResidual ≡ true
    communityAuthorityRemainsNonLegalAuthorityDomain : Bool
    communityAuthorityRemainsNonLegalAuthorityDomainIsTrue :
      communityAuthorityRemainsNonLegalAuthorityDomain ≡ true
    assessedDeltaMayRecomputeCalibration : Bool
    assessedDeltaMayRecomputeCalibrationIsTrue : assessedDeltaMayRecomputeCalibration ≡ true
    searchCompletionEqualsOperationalPayment : Bool
    searchCompletionEqualsOperationalPaymentIsFalse :
      searchCompletionEqualsOperationalPayment ≡ false
    formalClosureEqualsWorldRepair : Bool
    formalClosureEqualsWorldRepairIsFalse : formalClosureEqualsWorldRepair ≡ false

canonicalCountryV02ProofSearchBoundary : CountryV02ProofSearchBoundary
canonicalCountryV02ProofSearchBoundary = country-v02-proof-search-boundary
  true refl
  true refl
  true refl
  true refl
  true refl
  false refl
  false refl
