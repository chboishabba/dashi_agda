module DASHI.Cognition.PNF.SensibLawCountryOperationalResidualProofSearchBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.PluralEpistemicOperationalClosureExact as Operational
import DASHI.Core.PluralOperationalResidualActionLoopExact as Adaptive
import DASHI.Cognition.PNF.SensibLawCountryPluralEpistemicOperationalAuditExact as Audit
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search
import DASHI.Law.SensibLawProofSearchResultAssessmentExact as Assessment

------------------------------------------------------------------------
-- COUNTRY OPERATIONAL RESIDUAL -> PROOF-DIRECTED SEARCH
--
-- The operational-justice lane now lowers its first missing coordinate into
-- the already-owned proof-directed research ABI.  The residual determines the
-- required producer/source role before any provider or query string is chosen.
-- Community authority is deliberately not identified with legal authority.
------------------------------------------------------------------------

data OperationalSourceRole : Set where
  affectedCommunityOriginatingSource
  affectedCommunityAuthorityBearingSource
  realisedMaterialEffectSource
  independentMonitoringSource
  institutionalCorrectionOperationSource
  longitudinalRecurrenceSource
  : OperationalSourceRole

producerForOperationalResidual : Adaptive.OperationalResidual → Search.ProducerClass
producerForOperationalResidual Adaptive.realisedEffectResidual = Search.empiricalEvidenceProducer
producerForOperationalResidual Adaptive.communityOutcomeResidual = Search.propositionSourceProducer
producerForOperationalResidual Adaptive.communityAuthorityResidual = Search.attributionProducer
producerForOperationalResidual Adaptive.monitoringResidual = Search.empiricalEvidenceProducer
producerForOperationalResidual Adaptive.correctionResponseResidual = Search.empiricalEvidenceProducer
producerForOperationalResidual Adaptive.recurrencePreventionResidual = Search.empiricalEvidenceProducer

sourceRoleForOperationalResidual : Adaptive.OperationalResidual → OperationalSourceRole
sourceRoleForOperationalResidual Adaptive.realisedEffectResidual = realisedMaterialEffectSource
sourceRoleForOperationalResidual Adaptive.communityOutcomeResidual = affectedCommunityOriginatingSource
sourceRoleForOperationalResidual Adaptive.communityAuthorityResidual = affectedCommunityAuthorityBearingSource
sourceRoleForOperationalResidual Adaptive.monitoringResidual = independentMonitoringSource
sourceRoleForOperationalResidual Adaptive.correctionResponseResidual = institutionalCorrectionOperationSource
sourceRoleForOperationalResidual Adaptive.recurrencePreventionResidual = longitudinalRecurrenceSource

modeForOperationalResidual : Adaptive.OperationalResidual → Search.SearchMode
modeForOperationalResidual Adaptive.realisedEffectResidual = Search.exploitKnownResidual
modeForOperationalResidual Adaptive.communityOutcomeResidual = Search.exploreVocabulary
modeForOperationalResidual Adaptive.communityAuthorityResidual = Search.exploreAuthorityFamily
modeForOperationalResidual Adaptive.monitoringResidual = Search.exploitKnownResidual
modeForOperationalResidual Adaptive.correctionResponseResidual = Search.exploitKnownResidual
modeForOperationalResidual Adaptive.recurrencePreventionResidual = Search.exploitKnownResidual

record OperationalResidualSearchContract (r : Adaptive.OperationalResidual) : Set₁ where
  constructor operationalResidualSearchContract
  field
    consumerReference : String
    targetReference : String
    producer : Search.ProducerClass
    producerExact : producer ≡ producerForOperationalResidual r
    sourceRole : OperationalSourceRole
    sourceRoleExact : sourceRole ≡ sourceRoleForOperationalResidual r
    searchMode : Search.SearchMode
    searchModeExact : searchMode ≡ modeForOperationalResidual r
    stateProxyMaySubstituteCommunityOutcome : Bool
    stateProxyMaySubstituteCommunityOutcomeIsFalse :
      stateProxyMaySubstituteCommunityOutcome ≡ false
    extractedPropositionTransfersCommunityAuthority : Bool
    extractedPropositionTransfersCommunityAuthorityIsFalse :
      extractedPropositionTransfersCommunityAuthority ≡ false
    retrievalPaysOperationalResidual : Bool
    retrievalPaysOperationalResidualIsFalse : retrievalPaysOperationalResidual ≡ false
    contractReference : String

open OperationalResidualSearchContract public

communityOutcomeSearchContract :
  OperationalResidualSearchContract Adaptive.communityOutcomeResidual
communityOutcomeSearchContract = operationalResidualSearchContract
  "Country operational-justice consumer"
  "affected-community-defined satisfactory outcome"
  Search.propositionSourceProducer refl
  affectedCommunityOriginatingSource refl
  Search.exploreVocabulary refl
  false refl
  false refl
  false refl
  "country/community-outcome/proof-search-contract/v1"

communityAuthoritySearchContract :
  OperationalResidualSearchContract Adaptive.communityAuthorityResidual
communityAuthoritySearchContract = operationalResidualSearchContract
  "Country operational-justice consumer"
  "authority-bearing community mandate for the selected outcome"
  Search.attributionProducer refl
  affectedCommunityAuthorityBearingSource refl
  Search.exploreAuthorityFamily refl
  false refl
  false refl
  false refl
  "country/community-authority/proof-search-contract/v1"

------------------------------------------------------------------------
-- Lowering into the existing provider-neutral SearchIntent carrier.
------------------------------------------------------------------------

searchBudgetFor : Adaptive.OperationalResidual → Search.SearchBudget
searchBudgetFor Adaptive.realisedEffectResidual = Search.searchBudget 8 32 1 "bounded realised-effect search"
searchBudgetFor Adaptive.communityOutcomeResidual = Search.searchBudget 8 32 1 "bounded community-outcome search"
searchBudgetFor Adaptive.communityAuthorityResidual = Search.searchBudget 8 32 1 "bounded community-authority search"
searchBudgetFor Adaptive.monitoringResidual = Search.searchBudget 8 32 1 "bounded independent-monitor search"
searchBudgetFor Adaptive.correctionResponseResidual = Search.searchBudget 8 32 1 "bounded correction-operation search"
searchBudgetFor Adaptive.recurrencePreventionResidual = Search.searchBudget 8 32 1 "bounded recurrence-prevention search"

authorityClassFor : Adaptive.OperationalResidual → Search.RequiredAuthorityClass
authorityClassFor Adaptive.realisedEffectResidual = Search.supportingSourcePermitted
authorityClassFor Adaptive.communityOutcomeResidual = Search.primaryTextRequired
authorityClassFor Adaptive.communityAuthorityResidual = Search.primaryTextRequired
authorityClassFor Adaptive.monitoringResidual = Search.supportingSourcePermitted
authorityClassFor Adaptive.correctionResponseResidual = Search.primaryTextRequired
authorityClassFor Adaptive.recurrencePreventionResidual = Search.supportingSourcePermitted

targetReferenceFor : Adaptive.OperationalResidual → String
targetReferenceFor Adaptive.realisedEffectResidual = "realised material effect for declared consumer"
targetReferenceFor Adaptive.communityOutcomeResidual = "affected-community-defined satisfactory outcome"
targetReferenceFor Adaptive.communityAuthorityResidual = "community authority for selected outcome"
targetReferenceFor Adaptive.monitoringResidual = "independent/community-sensitive monitoring observation"
targetReferenceFor Adaptive.correctionResponseResidual = "institutional correction changed realised operation"
targetReferenceFor Adaptive.recurrencePreventionResidual = "observed prevention of recurrence"

searchIntentForOperationalResidual : Adaptive.OperationalResidual → Search.SearchIntent
searchIntentForOperationalResidual r = Search.searchIntent
  "Country operational-justice consumer"
  (targetReferenceFor r)
  (producerForOperationalResidual r)
  (modeForOperationalResidual r)
  "Australia / relevant Country and community"
  "consumer-relative current/historical envelope"
  (authorityClassFor r)
  "Two-Eyed operational evidence braid; retain strand provenance"
  "no provider selected before residual compilation"
  "same consumer, source role and authority domain required"
  "exclude State proxy substitution; exclude authority transfer; exclude retrieval-as-payment"
  (searchBudgetFor r)
  "country-operational-residual/search-intent/v1"

currentFirstResidual : Adaptive.OperationalResidual
currentFirstResidual =
  Adaptive.residualFor Operational.communityDefinedOutcomeCoordinate

currentFirstResidualExact : currentFirstResidual ≡ Adaptive.communityOutcomeResidual
currentFirstResidualExact = refl

currentFirstProducerExact :
  Search.producerClass (searchIntentForOperationalResidual currentFirstResidual)
  ≡ Search.propositionSourceProducer
currentFirstProducerExact = refl

currentFirstModeExact :
  Search.mode (searchIntentForOperationalResidual currentFirstResidual)
  ≡ Search.exploreVocabulary
currentFirstModeExact = refl

currentSnapshotFirstStepExact :
  Adaptive.firstOpen Audit.currentCountryOperationalSnapshot
  ≡ Adaptive.actOnCommunityOutcome
currentSnapshotFirstStepExact = refl

------------------------------------------------------------------------
-- Assessed frontier deltas, not raw retrieval, drive recomputation.
------------------------------------------------------------------------

data OperationalRecomputeAction : Set where
  keepSearchingSameResidual
  recomputeOperationalSnapshot
  reopenOperationalCoordinate
  inspectUnderidentification
  retainContestedState
  : OperationalRecomputeAction

recomputeActionFor : Assessment.FrontierChange → OperationalRecomputeAction
recomputeActionFor Assessment.frontierUnchanged = keepSearchingSameResidual
recomputeActionFor Assessment.frontierNarrowed = recomputeOperationalSnapshot
recomputeActionFor Assessment.frontierReopened = reopenOperationalCoordinate
recomputeActionFor Assessment.frontierClosed = recomputeOperationalSnapshot
recomputeActionFor Assessment.frontierContradicted = retainContestedState
recomputeActionFor Assessment.frontierUnderidentified = inspectUnderidentification

record OperationalJusticeFrontierDelta : Set₁ where
  constructor operationalJusticeFrontierDelta
  field
    residualBefore : Adaptive.OperationalResidual
    assessedDelta : Assessment.SearchFrontierDelta
    action : OperationalRecomputeAction
    actionExact : action ≡ recomputeActionFor (Assessment.change assessedDelta)
    sameConsumerReference : String
    provenanceLineageReference : String
    authorityLineageReference : String
    deltaReference : String

open OperationalJusticeFrontierDelta public

------------------------------------------------------------------------
-- Fail-closed boundaries.
------------------------------------------------------------------------

data SearchCompletionPaysOperationalResidual : Set where
data CommunityPropositionIsCommunityAuthority : Set where
data LegalAuthorityClassifiesCommunityMandate : Set where
data FrontierClosedMeansWorldStateJusticeClosed : Set where

data MoreStateDocumentsCanReplaceCommunityOutcomeSearch : Set where

searchCompletionDoesNotPayOperationalResidual :
  SearchCompletionPaysOperationalResidual → ⊥
searchCompletionDoesNotPayOperationalResidual ()

communityPropositionDoesNotCreateCommunityAuthority :
  CommunityPropositionIsCommunityAuthority → ⊥
communityPropositionDoesNotCreateCommunityAuthority ()

legalAuthorityDoesNotClassifyCommunityMandate :
  LegalAuthorityClassifiesCommunityMandate → ⊥
legalAuthorityDoesNotClassifyCommunityMandate ()

frontierClosureDoesNotManufactureWorldJustice :
  FrontierClosedMeansWorldStateJusticeClosed → ⊥
frontierClosureDoesNotManufactureWorldJustice ()

moreStateDocumentsDoNotReplaceCommunityOutcomeSearch :
  MoreStateDocumentsCanReplaceCommunityOutcomeSearch → ⊥
moreStateDocumentsDoNotReplaceCommunityOutcomeSearch ()

record OperationalResidualProofSearchBoundary : Set where
  constructor operationalResidualProofSearchBoundary
  field
    residualPrecedesProviderSelection : Bool
    residualPrecedesProviderSelectionIsTrue : residualPrecedesProviderSelection ≡ true
    communityOutcomeUsesCommunityOriginatingSourceRole : Bool
    communityOutcomeUsesCommunityOriginatingSourceRoleIsTrue :
      communityOutcomeUsesCommunityOriginatingSourceRole ≡ true
    communityAuthorityRemainsDistinctFromLegalAuthority : Bool
    communityAuthorityRemainsDistinctFromLegalAuthorityIsTrue :
      communityAuthorityRemainsDistinctFromLegalAuthority ≡ true
    rawRetrievalPaysResidual : Bool
    rawRetrievalPaysResidualIsFalse : rawRetrievalPaysResidual ≡ false
    assessedDeltaMayRecomputeOperationalSnapshot : Bool
    assessedDeltaMayRecomputeOperationalSnapshotIsTrue :
      assessedDeltaMayRecomputeOperationalSnapshot ≡ true
    formalFrontierClosureEqualsWorldStateClosure : Bool
    formalFrontierClosureEqualsWorldStateClosureIsFalse :
      formalFrontierClosureEqualsWorldStateClosure ≡ false

canonicalOperationalResidualProofSearchBoundary : OperationalResidualProofSearchBoundary
canonicalOperationalResidualProofSearchBoundary = operationalResidualProofSearchBoundary
  true refl
  true refl
  true refl
  false refl
  true refl
  false refl
