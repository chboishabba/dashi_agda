module DASHI.Cognition.PNF.SensibLawCountryCommunityOutcomeCandidateV02Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawCountryRealisedRepairProofSearchBridgeV02Exact as Bridge
import DASHI.Law.ComparativeSettlerColonialSovereigntySourceBidiExact as Sovereignty
import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as IK
import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- COMMUNITY-ORIGINATING OUTCOME CANDIDATE V02
--
-- The repository already carries the Uluru Statement as a source-bounded
-- First Nations consensus statement.  That is stronger than a State proxy and
-- is useful input to the first residual, but it is not silently promoted to a
-- consumer-specific operational outcome or a present authority mandate.
------------------------------------------------------------------------

data CommunityOutcomeCandidateStatus : Set where
  communityOriginatingCandidate
  consumerMatchedOutcomeAdmitted
  : CommunityOutcomeCandidateStatus

record CommunityOutcomeCandidate : Set where
  constructor community-outcome-candidate
  field
    sourceReceipt : Sovereignty.SovereigntySourceReceipt
    candidateStatus : CommunityOutcomeCandidateStatus
    consumerReference : String
    propositionReference : String
    communityOriginating : Bool
    communityOriginatingIsTrue : communityOriginating ≡ true
    sourceRoleIsFirstNationsConsensus :
      Sovereignty.role sourceReceipt ≡ Sovereignty.firstNationsConsensusStatement
    consumerSpecificOutcomePayment : Bool
    consumerSpecificOutcomePaymentIsFalse : consumerSpecificOutcomePayment ≡ false
    currentAuthorityScopeResolved : Bool
    currentAuthorityScopeResolvedIsFalse : currentAuthorityScopeResolved ≡ false
    candidateReference : String

open CommunityOutcomeCandidate public

uluruNeverCededCandidate : CommunityOutcomeCandidate
uluruNeverCededCandidate = community-outcome-candidate
  Sovereignty.uluruNeverCededReceipt
  communityOriginatingCandidate
  "Country / sovereignty / self-determination consumer family; exact consumer payment unresolved"
  "First Nations delegates state sovereignty has never been ceded or extinguished"
  true refl refl
  false refl
  false refl
  "uluru-2017/never-ceded/community-outcome-candidate/v02"

uluruCoexistenceCandidate : CommunityOutcomeCandidate
uluruCoexistenceCandidate = community-outcome-candidate
  Sovereignty.uluruCoexistenceReceipt
  communityOriginatingCandidate
  "Country / sovereignty / self-determination consumer family; exact consumer payment unresolved"
  "First Nations sovereignty co-exists with Crown sovereignty"
  true refl refl
  false refl
  false refl
  "uluru-2017/coexistence/community-outcome-candidate/v02"

uluruNeverCededHasCommunityConsensusRole :
  Sovereignty.role (sourceReceipt uluruNeverCededCandidate)
  ≡ Sovereignty.firstNationsConsensusStatement
uluruNeverCededHasCommunityConsensusRole = refl

uluruCandidateDoesNotPayConsumerOutcome :
  consumerSpecificOutcomePayment uluruNeverCededCandidate ≡ false
uluruCandidateDoesNotPayConsumerOutcome = refl

uluruCandidateDoesNotResolveCurrentAuthorityScope :
  currentAuthorityScopeResolved uluruNeverCededCandidate ≡ false
uluruCandidateDoesNotResolveCurrentAuthorityScope = refl

------------------------------------------------------------------------
-- Candidate acquisition narrows the same residual.  It does not jump to the
-- authority coordinate merely because the source is community-originating.
------------------------------------------------------------------------

candidateDeltaKeepsOutcomeResidualLive :
  DASHI.Law.SensibLawProofSearchResultAssessmentExact.firstResidualAfterReference
    Bridge.communityOutcomeCandidateDeltaV02
  ≡ "affectedCommunityOutcomeResidualV02"
candidateDeltaKeepsOutcomeResidualLive = refl

------------------------------------------------------------------------
-- Existing Two-Eyed authority non-factorability remains the reason this cannot
-- be flattened into proposition -> authority.
------------------------------------------------------------------------

extractedPropositionCannotRecoverCommunityAuthority :
  INF.FactorsThrough IK.extractedProposition IK.authority → ⊥
extractedPropositionCannotRecoverCommunityAuthority = IK.propositionCannotRecoverAuthority

data FirstNationsConsensusStatementPaysEveryCountryConsumer : Set where
data HistoricalConsensusStatementFixesPresentAuthorityScope : Set where
data CommunityOriginAutomaticallyMeansConsumerMatch : Set where

consensusStatementDoesNotPayEveryConsumer :
  FirstNationsConsensusStatementPaysEveryCountryConsumer → ⊥
consensusStatementDoesNotPayEveryConsumer ()

historicalConsensusDoesNotFixPresentAuthorityScope :
  HistoricalConsensusStatementFixesPresentAuthorityScope → ⊥
historicalConsensusDoesNotFixPresentAuthorityScope ()

communityOriginDoesNotAutomaticallyMeanConsumerMatch :
  CommunityOriginAutomaticallyMeansConsumerMatch → ⊥
communityOriginDoesNotAutomaticallyMeanConsumerMatch ()
