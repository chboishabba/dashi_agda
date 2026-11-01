module DASHI.Culture.MissingDeceasedTwentyScientistRound48AntiEchoChamberMethodologyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistRound47ForeignSourceStrataExact as R47
import DASHI.Interop.GodsEyeViewProofCarryingWorldOntologyExact as Anti

------------------------------------------------------------------------
-- ROUND 48: ANTI-ECHO-CHAMBER METHODOLOGY
--
-- This owner formalises a source-diversity and anti-confirmation-bias boundary
-- for the missing/deceased-scientist investigation.  It cross-pollinates the
-- repository anti-panopticon rule that visibility is not omniscience and
-- observation is not authority.
--
-- External methodological inspirations are source-attributed below.  Their
-- names do not import theorem authority into DASHI.  The exact combination of
-- source-family accounting, counter-source search, narrative projection and
-- anti-panopticon constraints is DASHI synthesis.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Source independence is not source count.
------------------------------------------------------------------------

data SourceIndependenceClass : Set where
  commonOriginCopy : SourceIndependenceClass
  sameInstitutionDerivative : SourceIndependenceClass
  independentPrimaryInstitutional : SourceIndependenceClass
  independentRegionalReporting : SourceIndependenceClass
  independentSkepticalReporting : SourceIndependenceClass
  independentComparativeReporting : SourceIndependenceClass
  officialInquiryRecord : SourceIndependenceClass
  unresolvedIndependence : SourceIndependenceClass

record SourceFamilyReceipt : Set where
  constructor source-family-receipt
  field
    sourceLabel : String
    sourceFamilyReference : String
    sourceOriginReference : String
    independenceClass : SourceIndependenceClass
    claimReference : String
    supportsClaim : Bool
    qualifiesClaim : Bool
    contradictsClaim : Bool
    provenanceInspectable : Bool
    copiedFromKnownOrigin : Bool

open SourceFamilyReceipt public

sourceCountDoesNotEqualIndependentEvidenceCount : Bool
sourceCountDoesNotEqualIndependentEvidenceCount = true

agreementAcrossDependentCopiesDoesNotMultiplyEvidence : Bool
agreementAcrossDependentCopiesDoesNotMultiplyEvidence = true

sameInstitutionDerivativesDoNotAutomaticallyBecomeIndependent : Bool
sameInstitutionDerivativesDoNotAutomaticallyBecomeIndependent = true

unresolvedIndependenceCannotBeSilentlyCountedAsIndependent : Bool
unresolvedIndependenceCannotBeSilentlyCountedAsIndependent = true

------------------------------------------------------------------------
-- 2. Claim-indexed search must include counter-source search.
------------------------------------------------------------------------

record ClaimSearchBoundary : Set where
  constructor claim-search-boundary
  field
    claimReference : String
    supportingSourceSearchReference : String
    qualifyingSourceSearchReference : String
    contradictingSourceSearchReference : String
    sourceOriginTraceReference : String
    searchedFamiliesReference : String
    coverageReference : String
    counterSourceSearchPerformed : Bool
    searchWasClaimIndexed : Bool
    searchWasPersonSurveillanceSweep : Bool

open ClaimSearchBoundary public

counterSourceSearchRequired : Bool
counterSourceSearchRequired = true

claimIndexedSearchPreferredOverNarrativeIndexedSearch : Bool
claimIndexedSearchPreferredOverNarrativeIndexedSearch = true

personSurveillanceSweepRequired : Bool
personSurveillanceSweepRequired = false

------------------------------------------------------------------------
-- 3. Disagreement is evidence about the source surface; it is not averaged
--    away by majority vote.
------------------------------------------------------------------------

data SourceDisagreementStatus : Set where
  noMaterialDisagreementLocated : SourceDisagreementStatus
  wordingDifference : SourceDisagreementStatus
  factualQualification : SourceDisagreementStatus
  factualConflict : SourceDisagreementStatus
  unresolvedSourceConflict : SourceDisagreementStatus

record DisagreementReceipt : Set where
  constructor disagreement-receipt
  field
    propositionReference : String
    sourceAReference : String
    sourceBReference : String
    disagreementStatus : SourceDisagreementStatus
    resolutionReference : String
    unresolvedDifferenceRetained : Bool

open DisagreementReceipt public

disagreementMustRemainVisible : Bool
disagreementMustRemainVisible = true

majorityVoteCannotReplaceClaimLevelResolution : Bool
majorityVoteCannotReplaceClaimLevelResolution = true

skepticalSourceDoesNotReceiveAutomaticPriority : Bool
skepticalSourceDoesNotReceiveAutomaticPriority = true

supportiveSourceDoesNotReceiveAutomaticPriority : Bool
supportiveSourceDoesNotReceiveAutomaticPriority = true

------------------------------------------------------------------------
-- 4. Narrative projection preserves provenance and epistemic status.
------------------------------------------------------------------------

record NarrativeProjectionBoundary : Set where
  constructor narrative-projection-boundary
  field
    propositionReference : String
    sourceFamilyReferences : String
    sourceOriginReferences : String
    supportingEvidenceReference : String
    qualifyingEvidenceReference : String
    contradictingEvidenceReference : String
    unresolvedEvidenceReference : String
    narrativeStatusReference : String
    projectionReference : String
    provenanceSurvivesProjection : Bool
    disagreementSurvivesProjection : Bool

open NarrativeProjectionBoundary public

provenanceMustSurviveNarrativeProjection : Bool
provenanceMustSurviveNarrativeProjection = true

disagreementMustSurviveNarrativeProjection : Bool
disagreementMustSurviveNarrativeProjection = true

narrativeSummaryCannotCreateSourceAuthority : Bool
narrativeSummaryCannotCreateSourceAuthority = true

------------------------------------------------------------------------
-- 5. Coverage and negative evidence reuse the anti-panopticon principle:
--    absence is assertable only over an actually covered source/property
--    family.  Search failure outside covered scope remains unresolved.
------------------------------------------------------------------------

absenceOutsideCoveredSearchRemainsUnresolved : Bool
absenceOutsideCoveredSearchRemainsUnresolved = true

searchEngineNoHitDoesNotEqualHistoricalAbsence : Bool
searchEngineNoHitDoesNotEqualHistoricalAbsence = true

foreignSourceNoHitDoesNotEqualSuppression : Bool
foreignSourceNoHitDoesNotEqualSuppression = true

------------------------------------------------------------------------
-- 6. Anti-panopticon cross-pollination.
--
-- The investigation may inspect public, relevant evidence needed to resolve a
-- claim.  It does not acquire general authority to surveil people, relatives,
-- associates or bystanders.  More coordinates may improve resolution without
-- creating intervention or surveillance authority.
------------------------------------------------------------------------

antiPanopticonBoundaryAnchor : Anti.AntiPanopticonBoundary
antiPanopticonBoundaryAnchor = Anti.canonicalAntiPanopticonBoundary

antiEchoChamberDoesNotCreateSurveillanceAuthority : Bool
antiEchoChamberDoesNotCreateSurveillanceAuthority = true

sourceDiversificationDoesNotAuthorizePrivateDataCollection : Bool
sourceDiversificationDoesNotAuthorizePrivateDataCollection = true

publicAvailabilityDoesNotErasePurposeLimitation : Bool
publicAvailabilityDoesNotErasePurposeLimitation = true

bystanderCollectionMustRemainOutOfScope : Bool
bystanderCollectionMustRemainOutOfScope = true

moreSourceCoordinatesDoNotCreateInterventionAuthority : Bool
moreSourceCoordinatesDoNotCreateInterventionAuthority = true

------------------------------------------------------------------------
-- 7. Hypothesis discipline.
--
-- The purpose of source diversification is not to locate a source that agrees
-- with a preferred story.  Evidence is tested against multiple live models.
------------------------------------------------------------------------

data CohortHypothesis : Set where
  distributedIndependentProgrammes : CohortHypothesis
  linkedSubclusters : CohortHypothesis
  oneCommonProgramme : CohortHypothesis
  coordinatedTargeting : CohortHypothesis

record HypothesisTestBoundary : Set where
  constructor hypothesis-test-boundary
  field
    hypothesis : CohortHypothesis
    diagnosticEvidenceReference : String
    inconsistentEvidenceReference : String
    missingDiscriminatorReference : String
    nextObservationReference : String
    falsificationSearchReference : String

open HypothesisTestBoundary public

preferredNarrativeCannotChooseEvidence : Bool
preferredNarrativeCannotChooseEvidence = true

hypothesesMustRemainCompetingUntilDiscriminated : Bool
hypothesesMustRemainCompetingUntilDiscriminated = true

oneCommonProgrammeStillRequiresLiteralH2Receipt : Bool
oneCommonProgrammeStillRequiresLiteralH2Receipt = true

coordinatedTargetingStillRequiresH3Receipt : Bool
coordinatedTargetingStillRequiresH3Receipt = true

------------------------------------------------------------------------
-- 8. External methodological attribution.
------------------------------------------------------------------------

record MethodAttribution : Set where
  constructor method-attribution
  field
    methodName : String
    sourceOwner : String
    sourceReference : String
    importedIdea : String
    notImportedAsAuthority : String

open MethodAttribution public

analysisOfCompetingHypothesesAttribution : MethodAttribution
analysisOfCompetingHypothesesAttribution = method-attribution
  "Analysis of Competing Hypotheses / structured analytic techniques"
  "Richards J. Heuer / CIA Center for the Study of Intelligence"
  "Psychology of Intelligence Analysis; A Tradecraft Primer; Studies in Intelligence"
  "maintain multiple hypotheses, identify diagnostic evidence, seek inconsistent/disconfirming evidence, and report sensitivity"
  "CIA attribution does not create factual authority over this cohort and does not make DASHI an intelligence-agency method clone"

analysisOfCompetingHypothesesAttributed : Bool
analysisOfCompetingHypothesesAttributed = true

lateralReadingAttribution : MethodAttribution
lateralReadingAttribution = method-attribution
  "lateral reading / civic online reasoning"
  "Stanford History Education Group / Digital Inquiry Group Civic Online Reasoning"
  "Lateral Reading on the Open Internet and related COR research"
  "leave the focal page to inspect who is behind a source and what independent sources say"
  "lateral reading does not convert reputation or search-engine ranking into truth"

lateralReadingAttributed : Bool
lateralReadingAttributed = true

bellingcatValidationAttribution : MethodAttribution
bellingcatValidationAttribution = method-attribution
  "open-source source validation and public-interest data collection"
  "Bellingcat"
  "Editorial Standards & Practices; Principles for Data Collection"
  "name sources, validate anonymous-source leads with reproducible open-source evidence, consider harm, privacy, public interest and alternatives"
  "Bellingcat practice does not create authority to collect irrelevant private data or to transfer an anonymous claim into fact"

bellingcatValidationAttributed : Bool
bellingcatValidationAttributed = true

adversarialCollaborationAttribution : MethodAttribution
adversarialCollaborationAttribution = method-attribution
  "adversarial collaboration"
  "scientific adversarial-collaboration literature / Nature editorial discussion"
  "Nature 2025-2026 discussion of rival-theory proponents jointly designing discriminating tests"
  "design observations capable of changing the minds of proponents of competing explanations"
  "adversarial collaboration does not require false balance or equal prior plausibility"

adversarialCollaborationAttributed : Bool
adversarialCollaborationAttributed = true

------------------------------------------------------------------------
-- 9. Current application to the scientist investigation.
------------------------------------------------------------------------

record CurrentAntiEchoChamberState : Set where
  constructor current-anti-echo-chamber-state
  field
    usOfficialInquiryFamilyPresent : Bool
    chinaDomesticFamilyPresent : Bool
    hongKongIndependentFamilyPresent : Bool
    indianComparativeFamilyPresent : Bool
    britishSkepticalFamilyPresent : Bool
    sourceOriginsTrackedSeparately : Bool
    counterNarrativeSourcesRetained : Bool
    currentSharedObjectPaid : Bool
    currentTargetingPaid : Bool

canonicalCurrentAntiEchoChamberState : CurrentAntiEchoChamberState
canonicalCurrentAntiEchoChamberState = current-anti-echo-chamber-state
  true true true true true true true false false

round48H2PaidCount : Nat
round48H2PaidCount = 0

round48H3PaidCount : Nat
round48H3PaidCount = 0

round48Narrative : String
round48Narrative = "Anti-echo-chamber discipline requires claim-indexed source diversification with source-origin accounting, not agreement-counting. Chinese institutional, Hong Kong, Indian comparative, British skeptical and U.S. official sources remain distinct provenance families. Supporting, qualifying and contradicting evidence stay visible through narrative projection. Search failure outside covered source families remains unresolved. Cross-pollinated anti-panopticon rules prevent source diversification from becoming general person-level surveillance: visibility is not omniscience, observation is not authority, public availability does not erase purpose limitation, and provenance must survive projection."

round48Pareto : String
round48Pareto = "For each high-alpha H1-to-H2 leaf, build a claim-source matrix with source-origin families, deliberately acquire at least one qualifying or contradicting source where available, collapse syndicated copies to one origin family, record covered versus uninspected search surfaces, and prefer observations that discriminate distributed-programme, linked-subcluster, common-programme and targeting hypotheses. Do not broaden into private-person surveillance or bystander collection."
