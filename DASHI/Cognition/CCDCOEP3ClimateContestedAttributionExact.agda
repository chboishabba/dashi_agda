module DASHI.Cognition.CCDCOEP3ClimateContestedAttributionExact where

------------------------------------------------------------------------
-- CASE-SPECIFIC SOURCE CONTESTATION, AUTHORISATION AND EXECUTION.
--
-- Historical sources:
-- 1998-04-27 Congressional Record, H2323-H2327: draft API meeting plan.
-- 1998-05-01 Living on Earth interview: attributed API VP response
-- reporting initiative of a lower-level employee; advocacy criticism.
-- 2017-09-05 Washington Post: documented later Cooler Heads advocacy
-- and interviews about its decentralised structure and funding.
-- 2019-10-23 House hearing: subsequent testimony about the 1998 plan.
--
-- Source relevance is not evidence that every plan was implemented,
-- nor that later Coalition acts were on the same execution authority.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.DiscriminatorSynthesisExact as D
import DASHI.Cognition.CCDCOEP3API1998PrimaryPlanExact as Plan

data AttributionQuestion : Set where
  planExisted : AttributionQuestion
  groupDraftedPlan : AttributionQuestion
  apiInstitutionApprovedPlan : AttributionQuestion
  specificTacticsImplemented : AttributionQuestion
  campaignCausedOpinionEffect : AttributionQuestion

data SourceDisposition : Set where
  primaryDocument : SourceDisposition
  attributedDenial : SourceDisposition
  investigation : SourceDisposition
  hearingTestimony : SourceDisposition

data HistoricalSource : Set where
  congressionalPlan1998 : HistoricalSource
  attributedAPIResponse1998 : HistoricalSource
  laterCoalitionInvestigation2017 : HistoricalSource
  laterCongressionalHearing2019 : HistoricalSource

sourceDisposition : HistoricalSource → SourceDisposition
sourceDisposition congressionalPlan1998 = primaryDocument
sourceDisposition attributedAPIResponse1998 = attributedDenial
sourceDisposition laterCoalitionInvestigation2017 = investigation
sourceDisposition laterCongressionalHearing2019 = hearingTestimony

-- Evidence categories cannot be substituted as interchangeable data,
-- even if a summary flattens all documents into 'climate campaigning'.
data FlattenedTopic : Set where
  climateDebate : FlattenedTopic

flattenSource : HistoricalSource → FlattenedTopic
flattenSource _ = climateDebate

primaryAndDenialDifferent :
  sourceDisposition congressionalPlan1998
  ≡ sourceDisposition attributedAPIResponse1998 → ⊥
primaryAndDenialDifferent ()

sourceKindNotIdentifiedByTopic :
  NF.FactorsThrough flattenSource sourceDisposition → ⊥
sourceKindNotIdentifiedByTopic =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness
      congressionalPlan1998
      attributedAPIResponse1998
      refl primaryAndDenialDifferent)

sourceTypeProbe : D.ExperimentBundle HistoricalSource
sourceTypeProbe =
  D.experimentBundle
    SourceDisposition
    sourceDisposition
    1
    "Retain documentary source type, speaker and original claim scope"
    "Source metadata known; not a campaign execution/outcome measurement"

sourceTypeSeparates :
  D.BundleSeparates sourceTypeProbe
    congressionalPlan1998 attributedAPIResponse1998
sourceTypeSeparates =
  D.bundleSeparates primaryAndDenialDifferent

sourceTypeLanguageExtension :
  D.DiscriminatingLanguageExtension flattenSource
sourceTypeLanguageExtension =
  D.discriminatingLanguageExtension
    (D.currentObserverCollision
      congressionalPlan1998 attributedAPIResponse1998 refl)
    sourceTypeProbe sourceTypeSeparates

-- Same confirmed publicly accessible draft can accompany incompatible
-- interpretations of whether API leadership later authorised it.
data InstitutionalAuthorityState : Set where
  approvalAbsent : InstitutionalAuthorityState
  approvalPresent : InstitutionalAuthorityState
  approvalStillUnresolved : InstitutionalAuthorityState

data AuthorityWorld : Set where
  unapprovedWorld : AuthorityWorld
  approvedWorld : AuthorityWorld
  unresolvedWorld : AuthorityWorld

authorityHypothesis : AuthorityWorld → InstitutionalAuthorityState
authorityHypothesis unapprovedWorld = approvalAbsent
authorityHypothesis approvedWorld = approvalPresent
authorityHypothesis unresolvedWorld = approvalStillUnresolved

publishedDraft : AuthorityWorld → Plan.HistoricalActionStage
publishedDraft _ = Plan.draftRecorded

samePublishedDraft :
  publishedDraft unapprovedWorld ≡ publishedDraft approvedWorld
samePublishedDraft = refl

differentAuthorisation :
  authorityHypothesis unapprovedWorld
  ≡ authorityHypothesis approvedWorld → ⊥
differentAuthorisation ()

publishedDraftCannotProveInstitutionalAuthorisation :
  NF.FactorsThrough publishedDraft authorityHypothesis → ⊥
publishedDraftCannotProveInstitutionalAuthorisation =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness
      unapprovedWorld approvedWorld
      samePublishedDraft differentAuthorisation)

-- Prospective discriminator: an actual source-pinned organisational
-- adoption/vote/approved spending/approval record, not inference
-- from a rhetorical description by either disputant.
authorisationRecordProbe : D.ExperimentBundle AuthorityWorld
authorisationRecordProbe =
  D.experimentBundle
    InstitutionalAuthorityState
    authorityHypothesis
    1
    "Identify original signed authorisation, approval or expenditure records"
    "Synthetic oracle; actual authorisation archive is not yet admitted"

authorisationRecordWouldSeparate :
  D.BundleSeparates authorisationRecordProbe
    unapprovedWorld approvedWorld
authorisationRecordWouldSeparate =
  D.bundleSeparates differentAuthorisation

authorisationLanguageExtension :
  D.DiscriminatingLanguageExtension publishedDraft
authorisationLanguageExtension =
  D.discriminatingLanguageExtension
    (D.currentObserverCollision
      unapprovedWorld approvedWorld samePublishedDraft)
    authorisationRecordProbe authorisationRecordWouldSeparate

-- Separate treatment: verified later public coalition advocacy is not
-- a proof that the same 1998 API action plan was centrally implemented.
data DistinctHistoricalQuestion : Set where
  laterAdvocacyHappened : DistinctHistoricalQuestion
  executed1998Draft : DistinctHistoricalQuestion

data DirectCommandBridge : Set where

noAutomaticLaterAdvocacyTo1998Implementation :
  DirectCommandBridge → ⊥
noAutomaticLaterAdvocacyTo1998Implementation ()

-- The original sources are still separately addressable in case
-- evidence; no source-grade swap, temporal telescoping or auto-promotion.
