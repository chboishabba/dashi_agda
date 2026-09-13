module DASHI.Wikimedia.IbrahimSnowballEthnographyParticipantObservationFieldworkBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as Dewey
import DASHI.Wikimedia.IbrahimSnowballArchiveHistoriographyCausalityBidiExact as Archive
import DASHI.Wikimedia.IbrahimSnowballTestimonyMemoryCredibilityCorroborationExpertBidiExact as Testimony
import DASHI.Wikimedia.IbrahimSnowballSocialInfluenceConsentCoercionPrimarySourcesExact as Influence

------------------------------------------------------------------------
-- LIVE IBRAHIM RANK-1 COMPOSITION:
-- ethnography / participant observation / fieldwork.
--
-- This is a thin receipt over existing observer, testimony, archive, consent,
-- source-criticism and community-authority machinery. Participation in a field
-- setting does not manufacture informed consent, community authority, observer
-- neutrality, interpretation authority, or whole-system truth.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim ethnography/participant-observation fieldwork BIDI"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "Wikidata identity inspected 2026-09-11; identity does not create consent, observer neutrality, community authority, representativeness or truth")

ethnographyQid : Identity.ExternalIdentityDemand
ethnographyQid = mkQid "ethnography" "Q132151"

participantObservationQid : Identity.ExternalIdentityDemand
participantObservationQid = mkQid "participant observation" "Q1129049"

ethnographyDewey : Dewey.DeweyCoordinate
ethnographyDewey = Dewey.mkUnresolvedDewey
  "ethnography"
  "no exact inspected DDC value promoted in this pass"

participantObservationDewey : Dewey.DeweyCoordinate
participantObservationDewey = Dewey.mkUnresolvedDewey
  "participant observation"
  "method spans anthropology, sociology and applied/community research; no exact inspected DDC value promoted"

------------------------------------------------------------------------
-- DOI-bounded method sources.
------------------------------------------------------------------------

roqueCommunityParticipantObservationSource : Attribution.AttributedSource
roqueCommunityParticipantObservationSource = Attribution.mkDOISource
  "Anais Roque; Amber Wutich; Alexandra Brewis; Melissa Beresford; Laura Landes; Olga Morales-Pate; Ramon Lucero; Wendy Jepson; Yushiou Tsai; Michael Hanemann; Action for Water Equity Consortium"
  "Community-based Participant-observation (CBPO): A Participatory Method for Ethnographic Research"
  "Field Methods 36(1)"
  "2024"
  "10.1177/1525822X231198989"
  "https://doi.org/10.1177/1525822X231198989"
  Attribution.academicArticleSource
  "method paper centering community knowledge co-creation, community members as agentive observers, consent, field-note provenance and reporting-back; does not imply every participant-observation project has these properties"
  Attribution.publicAttribution

seimHybridEthnographySource : Attribution.AttributedSource
seimHybridEthnographySource = Attribution.mkDOISource
  "Josh Seim"
  "Participant Observation, Observant Participation, and Hybrid Ethnography"
  "Sociological Methods & Research 53(1)"
  "2024"
  "10.1177/0049124120986209"
  "https://doi.org/10.1177/0049124120986209"
  Attribution.academicArticleSource
  "method comparison distinguishing field positioning, analytic gaze and data assembly; participation intensity does not itself determine epistemic superiority"
  Attribution.publicAttribution

brearTsotetsiEthicsSource : Attribution.AttributedSource
brearTsotetsiEthicsSource = Attribution.mkDOISource
  "Michelle R. Brear; Cias T. Tsotetsi"
  "(De)colonising outcomes of community participation – a South African ethnography of ethics in practice"
  "Qualitative Research 22(6)"
  "2022"
  "10.1177/14687941211004417"
  "https://doi.org/10.1177/14687941211004417"
  Attribution.academicArticleSource
  "ethnographic analysis of community participation in consent/assent procedures and power relations; participation may shift power without automatically eliminating structural constraints"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Canonical fieldwork receipt.
------------------------------------------------------------------------

record FieldworkReceipt : Set where
  constructor fieldwork-receipt
  field
    methodIdentity : String
    observerRelation : String
    participantRole : String
    consentAssentState : String
    authorityRelation : String
    temporalScope : String
    fieldNoteProvenance : String
    interpretationOwner : String
    affectedSubjectVoice : String
    revisionOrReportingBackRoute : String
    sourceCriticismPaid : Bool
    observerPositionExplicit : Bool
    consentIndependentOfMereParticipation : Bool
    communityAuthorityIndependentOfResearchAccess : Bool
    wholeSystemTruthClaimed : Bool
open FieldworkReceipt public

canonicalFieldworkReceipt : FieldworkReceipt
canonicalFieldworkReceipt = fieldwork-receipt
  "ethnography / participant observation"
  "observer-participant relation must be explicit"
  "observed participant, participant-observer, community co-observer or other role must be retained"
  "consent/assent/opt-out state is a separate evidentiary and ethical coordinate"
  "research access and institutional permission do not create participant or community authority"
  "fieldwork time/window must travel with the observation"
  "field notes retain author, time, method and common-source genealogy"
  "analysis/interpretation attribution remains explicit"
  "participant/community interpretation may converge, diverge or remain silent"
  "report-back, correction and contextualisation remain available without rewriting historical field notes"
  true true true true false

------------------------------------------------------------------------
-- Regression 1: participation/visibility cannot recover consent.
------------------------------------------------------------------------

data ParticipationCase : Set where
  sameObservedParticipationConsented sameObservedParticipationNotConsented : ParticipationCase

data ParticipationSurface : Set where sameVisibleParticipation : ParticipationSurface
data ConsentStatus : Set where consentPaid consentNotPaid : ConsentStatus

participationSurface : ParticipationCase → ParticipationSurface
participationSurface _ = sameVisibleParticipation

consentStatus : ParticipationCase → ConsentStatus
consentStatus sameObservedParticipationConsented = consentPaid
consentStatus sameObservedParticipationNotConsented = consentNotPaid

participationConsentDefect : INF.NonFactorabilityWitness participationSurface consentStatus
participationConsentDefect = INF.nonFactorabilityWitness
  sameObservedParticipationConsented sameObservedParticipationNotConsented refl (λ ())

participationCannotFactorConsent :
  INF.FactorsThrough participationSurface consentStatus → ⊥
participationCannotFactorConsent =
  INF.witnessRulesOutEveryFlatFactorisation participationConsentDefect

------------------------------------------------------------------------
-- Regression 2: research/institutional access cannot recover community authority.
------------------------------------------------------------------------

data AccessCase : Set where
  sameResearchAccessCommunityAuthorityPaid sameResearchAccessCommunityAuthorityOpen : AccessCase

data AccessSurface : Set where sameInstitutionalResearchAccess : AccessSurface
data CommunityAuthority : Set where authorityPaid authorityOpen : CommunityAuthority

accessSurface : AccessCase → AccessSurface
accessSurface _ = sameInstitutionalResearchAccess

communityAuthority : AccessCase → CommunityAuthority
communityAuthority sameResearchAccessCommunityAuthorityPaid = authorityPaid
communityAuthority sameResearchAccessCommunityAuthorityOpen = authorityOpen

accessAuthorityDefect : INF.NonFactorabilityWitness accessSurface communityAuthority
accessAuthorityDefect = INF.nonFactorabilityWitness
  sameResearchAccessCommunityAuthorityPaid sameResearchAccessCommunityAuthorityOpen refl (λ ())

researchAccessCannotFactorCommunityAuthority :
  INF.FactorsThrough accessSurface communityAuthority → ⊥
researchAccessCannotFactorCommunityAuthority =
  INF.witnessRulesOutEveryFlatFactorisation accessAuthorityDefect

------------------------------------------------------------------------
-- Regression 3: same observed event cannot recover observer-position/reading.
------------------------------------------------------------------------

data ObserverCase : Set where
  sameEventExternalObserver sameEventCommunityObserver : ObserverCase

data ObservedSurface : Set where sameObservedEvent : ObservedSurface
data ObserverPosition : Set where externalResearcher communityParticipantObserver : ObserverPosition

observedSurface : ObserverCase → ObservedSurface
observedSurface _ = sameObservedEvent

observerPosition : ObserverCase → ObserverPosition
observerPosition sameEventExternalObserver = externalResearcher
observerPosition sameEventCommunityObserver = communityParticipantObserver

observerPositionDefect : INF.NonFactorabilityWitness observedSurface observerPosition
observerPositionDefect = INF.nonFactorabilityWitness
  sameEventExternalObserver sameEventCommunityObserver refl (λ ())

observationCannotFactorObserverPosition :
  INF.FactorsThrough observedSurface observerPosition → ⊥
observationCannotFactorObserverPosition =
  INF.witnessRulesOutEveryFlatFactorisation observerPositionDefect

------------------------------------------------------------------------
-- Regression 4: field-note convergence cannot recover whole-system truth.
------------------------------------------------------------------------

data FieldNoteCase : Set where
  sameConvergentNotesNarrowScope sameConvergentNotesDifferentUnobservedContext : FieldNoteCase

data FieldNoteSurface : Set where sameConvergentFieldNotes : FieldNoteSurface
data ScopeAdequacy : Set where adequateForBoundedQuestion insufficientForWholeSystem : ScopeAdequacy

fieldNoteSurface : FieldNoteCase → FieldNoteSurface
fieldNoteSurface _ = sameConvergentFieldNotes

scopeAdequacy : FieldNoteCase → ScopeAdequacy
scopeAdequacy sameConvergentNotesNarrowScope = adequateForBoundedQuestion
scopeAdequacy sameConvergentNotesDifferentUnobservedContext = insufficientForWholeSystem

fieldNoteScopeDefect : INF.NonFactorabilityWitness fieldNoteSurface scopeAdequacy
fieldNoteScopeDefect = INF.nonFactorabilityWitness
  sameConvergentNotesNarrowScope sameConvergentNotesDifferentUnobservedContext refl (λ ())

fieldNoteConvergenceCannotFactorWholeSystemAdequacy :
  INF.FactorsThrough fieldNoteSurface scopeAdequacy → ⊥
fieldNoteConvergenceCannotFactorWholeSystemAdequacy =
  INF.witnessRulesOutEveryFlatFactorisation fieldNoteScopeDefect

------------------------------------------------------------------------
-- Reuse existing source/evidence boundaries; no parallel epistemology.
------------------------------------------------------------------------

archiveBoundary : Archive.ArchiveHistoriographyCausalityBoundary
archiveBoundary = Archive.canonicalArchiveHistoriographyCausalityBoundary

testimonyBoundary : Testimony.TestimonyMemoryCredibilityBoundary
testimonyBoundary = Testimony.canonicalTestimonyMemoryCredibilityBoundary

------------------------------------------------------------------------
-- Reverse BIDI constraints.
------------------------------------------------------------------------

record FieldworkReverseConstraint : Set where
  constructor fieldwork-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open FieldworkReverseConstraint public

anthropologyConstraint : FieldworkReverseConstraint
anthropologyConstraint = fieldwork-reverse-constraint
  "Anthropology / ethnography"
  "method label, observer relation, participant role, field positioning, analytic gaze, source genealogy and interpretation remain distinct"
  false

communityConstraint : FieldworkReverseConstraint
communityConstraint = fieldwork-reverse-constraint
  "Community / affected-subject knowledge"
  "research access, participation, consent, community authority, participant voice and interpretation/revision power remain distinct"
  false

historyConstraint : FieldworkReverseConstraint
historyConstraint = fieldwork-reverse-constraint
  "Archive / historiography"
  "field note, observation time, later interpretation, correction and present use remain separate append-only provenance coordinates"
  false

scienceConstraint : FieldworkReverseConstraint
scienceConstraint = fieldwork-reverse-constraint
  "Observation / evidence"
  "observed event, observer position, measurement/report, bounded question, sampling scope and whole-system inference remain distinct"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data ParticipationCreatesConsent : Set where
data ResearchAccessCreatesCommunityAuthority : Set where
data ParticipantObservationCreatesNeutrality : Set where
data FieldNoteConvergenceCreatesWholeSystemTruth : Set where
data QidCreatesMethodValidity : Set where
data DeweyCreatesAuthority : Set where

participationDoesNotCreateConsent : ParticipationCreatesConsent → ⊥
participationDoesNotCreateConsent ()

researchAccessDoesNotCreateCommunityAuthority : ResearchAccessCreatesCommunityAuthority → ⊥
researchAccessDoesNotCreateCommunityAuthority ()

participantObservationDoesNotCreateNeutrality : ParticipantObservationCreatesNeutrality → ⊥
participantObservationDoesNotCreateNeutrality ()

fieldNoteConvergenceDoesNotCreateWholeSystemTruth : FieldNoteConvergenceCreatesWholeSystemTruth → ⊥
fieldNoteConvergenceDoesNotCreateWholeSystemTruth ()

qidDoesNotCreateMethodValidity : QidCreatesMethodValidity → ⊥
qidDoesNotCreateMethodValidity ()

deweyDoesNotCreateAuthority : DeweyCreatesAuthority → ⊥
deweyDoesNotCreateAuthority ()

record EthnographyParticipantObservationBoundary : Set where
  constructor ethnography-participant-observation-boundary
  field
    qidsAttachedWhenSafelyResolved : Bool
    deweyUnresolvedStateRetained : Bool
    doiSourceRolesRetained : Bool
    observerPositionRetained : Bool
    participationSeparatedFromConsent : Bool
    researchAccessSeparatedFromCommunityAuthority : Bool
    fieldNoteProvenanceRetained : Bool
    affectedSubjectVoiceAndRevisionRetained : Bool
    boundedObservationSeparatedFromWholeSystemTruth : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open EthnographyParticipantObservationBoundary public

canonicalEthnographyParticipantObservationBoundary : EthnographyParticipantObservationBoundary
canonicalEthnographyParticipantObservationBoundary =
  ethnography-participant-observation-boundary
    true true true true true true true true true true false
