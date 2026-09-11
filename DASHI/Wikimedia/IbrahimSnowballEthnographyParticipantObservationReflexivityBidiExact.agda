module DASHI.Wikimedia.IbrahimSnowballEthnographyParticipantObservationReflexivityBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as Dewey
import DASHI.Wikimedia.IbrahimEnglishAnthropologyHumanityBridgeExact as Anthropology
import DASHI.Wikimedia.IbrahimSnowballTestimonyMemoryCredibilityCorroborationExpertBidiExact as Testimony
import DASHI.Wikimedia.IbrahimSnowballArchiveHistoriographyCausalityBidiExact as Archive

------------------------------------------------------------------------
-- IBRAHIM / ETHNOGRAPHY / PARTICIPANT-OBSERVATION / REFLEXIVITY BIDI
--
-- The roadmap identifies ethnographic/participant-observation fieldwork as a
-- genuine method/provenance debt.  This owner pays that method seam without
-- turning generic observer machinery into ethnography or ethnographic presence
-- into participant consent, community authority, causal proof or complete
-- insider meaning.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim ethnography/participant-observation/reflexivity BIDI"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "Wikidata identity inspected 2026-09-11; identity does not create fieldwork quality, consent, insider authority, interpretation truth or causality")

ethnographyQid : Identity.ExternalIdentityDemand
ethnographyQid = mkQid "ethnography" "Q132151"

participantObservationQid : Identity.ExternalIdentityDemand
participantObservationQid = mkQid "participant observation" "Q1129049"

fieldResearchQid : Identity.ExternalIdentityDemand
fieldResearchQid = mkQid "field research / fieldwork" "Q1402508"

ethnographerQid : Identity.ExternalIdentityDemand
ethnographerQid = mkQid "ethnographer" "Q12347522"

anthropologyQid : Identity.ExternalIdentityDemand
anthropologyQid = mkQid "anthropology" "Q23404"

zlatanovicWorkQid : Identity.ExternalIdentityDemand
zlatanovicWorkQid = mkQid
  "Participant observation as a research method in anthropology: Advantages and constraints"
  "Q141276138"

------------------------------------------------------------------------
-- Dewey: retain exact inspected field-research values and leave the narrower
-- method identities unresolved rather than forcing them onto an adjacent shelf.
------------------------------------------------------------------------

fieldResearchDeweyGeneral : Dewey.DeweyCoordinate
fieldResearchDeweyGeneral = Dewey.mkVerifiedDewey
  "field research"
  "001.433"
  "Wikidata Q1402508 DDC statement inspected 2026-09-11"

fieldResearchDeweySocialScience : Dewey.DeweyCoordinate
fieldResearchDeweySocialScience = Dewey.mkVerifiedDewey
  "field research"
  "301.072"
  "Wikidata Q1402508 DDC statement inspected 2026-09-11; multiple coordinates retained"

ethnographyDewey : Dewey.DeweyCoordinate
ethnographyDewey = Dewey.mkUnresolvedDewey
  "ethnography"
  "no exact inspected DDC statement promoted for Q132151 in this pass"

participantObservationDewey : Dewey.DeweyCoordinate
participantObservationDewey = Dewey.mkUnresolvedDewey
  "participant observation"
  "no exact inspected DDC statement promoted for Q1129049 in this pass"

------------------------------------------------------------------------
-- Method-source attribution.
------------------------------------------------------------------------

burawoyReflexiveEthnographySource : Attribution.AttributedSource
burawoyReflexiveEthnographySource = Attribution.mkDOISource
  "Michael Burawoy"
  "Revisits: An Outline of a Theory of Reflexive Ethnography"
  "American Sociological Review 68(5)"
  "2003"
  "10.1177/000312240306800501"
  "https://doi.org/10.1177/000312240306800501"
  Attribution.academicArticleSource
  "methodological account of focused revisits and observer/theory/site/external-source differences; supports reflexive provenance, not a universal ethnographic ontology"
  Attribution.publicAttribution

roqueCommunityParticipantObservationSource : Attribution.AttributedSource
roqueCommunityParticipantObservationSource = Attribution.mkDOISource
  "Anais Roque; Amber Wutich; Alexandra Brewis; Melissa Beresford; Laura Landes; Olga Morales-Pate; Ramon Lucero; Wendy Jepson; Yushiou Tsai; Michael Hanemann; Action for Water Equity Consortium"
  "Community-based Participant-observation (CBPO): A Participatory Method for Ethnographic Research"
  "Field Methods 36(1)"
  "2024"
  "10.1177/1525822X231198989"
  "https://doi.org/10.1177/1525822X231198989"
  Attribution.academicArticleSource
  "community-based participant-observation method combining ethnographic participant observation with participatory research; collaboration does not automatically create full community authority or consent for every downstream use"
  Attribution.publicAttribution

zlatanovicParticipantObservationSource : Attribution.AttributedSource
zlatanovicParticipantObservationSource = Attribution.mkDOISource
  "Ljubisa Zlatanovic"
  "Participant observation as a research method in anthropology: Advantages and constraints"
  "Glasnik Antropoloskog Drustva Srbije 49"
  "2014"
  "10.5937/GADS1449167Z"
  "https://doi.org/10.5937/GADS1449167Z"
  Attribution.academicArticleSource
  "method paper on participant observation's strengths and constraints; exact work identity additionally retained as Q141276138"
  Attribution.publicAttribution

owusuFieldworkDataQualitySource : Attribution.AttributedSource
owusuFieldworkDataQualitySource = Attribution.mkDOISource
  "Maxwell Owusu"
  "Ethnography of Africa: The Usefulness of the Useless"
  "American Anthropologist 80(2)"
  "1978"
  "10.1525/aa.1978.80.2.02a00040"
  "https://doi.org/10.1525/aa.1978.80.2.02a00040"
  Attribution.academicArticleSource
  "methodological critique of data quality, ethnographer bias, language and interpreter/informant use; does not make any one language or observer position epistemically sufficient"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Regression 1: observed action cannot recover participant meaning.
------------------------------------------------------------------------

data ActionCase : Set where
  sameObservedActionMeaningA sameObservedActionMeaningB : ActionCase

data ObservedActionSurface : Set where sameObservedAction : ObservedActionSurface
data ParticipantMeaning : Set where participantMeaningA participantMeaningB : ParticipantMeaning

observedActionSurface : ActionCase → ObservedActionSurface
observedActionSurface _ = sameObservedAction

participantMeaning : ActionCase → ParticipantMeaning
participantMeaning sameObservedActionMeaningA = participantMeaningA
participantMeaning sameObservedActionMeaningB = participantMeaningB

actionMeaningDefect : INF.NonFactorabilityWitness observedActionSurface participantMeaning
actionMeaningDefect = INF.nonFactorabilityWitness
  sameObservedActionMeaningA sameObservedActionMeaningB refl (λ ())

observationCannotFactorParticipantMeaning :
  INF.FactorsThrough observedActionSurface participantMeaning → ⊥
observationCannotFactorParticipantMeaning =
  INF.witnessRulesOutEveryFlatFactorisation actionMeaningDefect

------------------------------------------------------------------------
-- Regression 2: fieldnote/report surface cannot recover observer relation.
------------------------------------------------------------------------

data FieldnoteCase : Set where
  sameFieldnoteParticipantRelation sameFieldnoteDetachedRelation : FieldnoteCase

data FieldnoteSurface : Set where sameFieldnoteText : FieldnoteSurface
data ObserverRelation : Set where participantRelated detachedObserverRelation : ObserverRelation

fieldnoteSurface : FieldnoteCase → FieldnoteSurface
fieldnoteSurface _ = sameFieldnoteText

observerRelation : FieldnoteCase → ObserverRelation
observerRelation sameFieldnoteParticipantRelation = participantRelated
observerRelation sameFieldnoteDetachedRelation = detachedObserverRelation

fieldnoteRelationDefect : INF.NonFactorabilityWitness fieldnoteSurface observerRelation
fieldnoteRelationDefect = INF.nonFactorabilityWitness
  sameFieldnoteParticipantRelation sameFieldnoteDetachedRelation refl (λ ())

fieldnoteCannotFactorObserverRelation :
  INF.FactorsThrough fieldnoteSurface observerRelation → ⊥
fieldnoteCannotFactorObserverRelation =
  INF.witnessRulesOutEveryFlatFactorisation fieldnoteRelationDefect

------------------------------------------------------------------------
-- Regression 3: participation/presence cannot recover consent or authority.
------------------------------------------------------------------------

data ParticipationCase : Set where
  sameParticipationConsentPaid sameParticipationConsentOpen : ParticipationCase

data ParticipationSurface : Set where sameFieldParticipation : ParticipationSurface
data ConsentAuthorityStatus : Set where consentAuthorityPaid consentAuthorityOpen : ConsentAuthorityStatus

participationSurface : ParticipationCase → ParticipationSurface
participationSurface _ = sameFieldParticipation

consentAuthorityStatus : ParticipationCase → ConsentAuthorityStatus
consentAuthorityStatus sameParticipationConsentPaid = consentAuthorityPaid
consentAuthorityStatus sameParticipationConsentOpen = consentAuthorityOpen

participationConsentDefect : INF.NonFactorabilityWitness participationSurface consentAuthorityStatus
participationConsentDefect = INF.nonFactorabilityWitness
  sameParticipationConsentPaid sameParticipationConsentOpen refl (λ ())

participantObservationCannotFactorConsentAuthority :
  INF.FactorsThrough participationSurface consentAuthorityStatus → ⊥
participantObservationCannotFactorConsentAuthority =
  INF.witnessRulesOutEveryFlatFactorisation participationConsentDefect

------------------------------------------------------------------------
-- Regression 4: revisit/multiplicity cannot recover independence.
------------------------------------------------------------------------

data RevisitCase : Set where
  sameRevisitCountIndependent sameRevisitCountDependent : RevisitCase

data RevisitSurface : Set where sameFieldworkMultiplicity : RevisitSurface
data RevisitIndependence : Set where independentRevisit commonTheoryOrSourceDependent : RevisitIndependence

revisitSurface : RevisitCase → RevisitSurface
revisitSurface _ = sameFieldworkMultiplicity

revisitIndependence : RevisitCase → RevisitIndependence
revisitIndependence sameRevisitCountIndependent = independentRevisit
revisitIndependence sameRevisitCountDependent = commonTheoryOrSourceDependent

revisitIndependenceDefect : INF.NonFactorabilityWitness revisitSurface revisitIndependence
revisitIndependenceDefect = INF.nonFactorabilityWitness
  sameRevisitCountIndependent sameRevisitCountDependent refl (λ ())

fieldworkMultiplicityCannotFactorIndependence :
  INF.FactorsThrough revisitSurface revisitIndependence → ⊥
fieldworkMultiplicityCannotFactorIndependence =
  INF.witnessRulesOutEveryFlatFactorisation revisitIndependenceDefect

------------------------------------------------------------------------
-- Existing boundaries are reused.
------------------------------------------------------------------------

anthropologyBoundary : Anthropology.AnthropologyHumanityBoundary
anthropologyBoundary = Anthropology.canonicalAnthropologyHumanityBoundary

testimonyBoundary : Testimony.TestimonyMemoryCredibilityBoundary
testimonyBoundary = Testimony.canonicalTestimonyMemoryCredibilityBoundary

archiveBoundary : Archive.ArchiveHistoriographyCausalityBoundary
archiveBoundary = Archive.canonicalArchiveHistoriographyCausalityBoundary

------------------------------------------------------------------------
-- Reverse BIDI constraints.
------------------------------------------------------------------------

record EthnographyReverseConstraint : Set where
  constructor ethnography-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open EthnographyReverseConstraint public

anthropologyConstraint : EthnographyReverseConstraint
anthropologyConstraint = ethnography-reverse-constraint
  "Anthropology / ethnography"
  "field site, participant relation, observation, fieldnote, participant interpretation, researcher interpretation, language/interpreter role, consent and source provenance remain distinct"
  false

communityConstraint : EthnographyReverseConstraint
communityConstraint = ethnography-reverse-constraint
  "Community / affected-subject knowledge"
  "research participation, self-description, collaboration, consent, custodial/community authority and downstream reuse permission remain distinct"
  false

historyConstraint : EthnographyReverseConstraint
historyConstraint = ethnography-reverse-constraint
  "History / archives / revisit"
  "earlier fieldnotes, later revisit, changed observer relation, changed theory, internal site change and external historical change remain separately attributable"
  false

scienceConstraint : EthnographyReverseConstraint
scienceConstraint = ethnography-reverse-constraint
  "Observation / replication / inference"
  "fieldwork multiplicity, observer dependence, methodological reproducibility, provenance independence and causal inference remain distinct"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data ObservationEqualsMeaning : Set where
data ParticipationEqualsConsent : Set where
data EthnographerEqualsInsiderAuthority : Set where
data FieldnoteEqualsParticipantVoice : Set where
data RevisitEqualsIndependentReplication : Set where
data QidCreatesEthnographicValidity : Set where
data DeweyCreatesMethodAuthority : Set where

observationDoesNotCreateParticipantMeaning : ObservationEqualsMeaning → ⊥
observationDoesNotCreateParticipantMeaning ()

participationDoesNotCreateConsent : ParticipationEqualsConsent → ⊥
participationDoesNotCreateConsent ()

ethnographerDoesNotCreateInsiderAuthority : EthnographerEqualsInsiderAuthority → ⊥
ethnographerDoesNotCreateInsiderAuthority ()

fieldnoteDoesNotBecomeParticipantVoice : FieldnoteEqualsParticipantVoice → ⊥
fieldnoteDoesNotBecomeParticipantVoice ()

revisitDoesNotCreateIndependentReplication : RevisitEqualsIndependentReplication → ⊥
revisitDoesNotCreateIndependentReplication ()

qidDoesNotCreateEthnographicValidity : QidCreatesEthnographicValidity → ⊥
qidDoesNotCreateEthnographicValidity ()

deweyDoesNotCreateMethodAuthority : DeweyCreatesMethodAuthority → ⊥
deweyDoesNotCreateMethodAuthority ()

record EthnographyParticipantObservationBoundary : Set where
  constructor ethnography-participant-observation-boundary
  field
    qidsAttachedWhenSafelyResolved : Bool
    multipleDeweyCoordinatesRetained : Bool
    doiAndCanonicalLinksRetained : Bool
    observedActionSeparatedFromParticipantMeaning : Bool
    fieldnoteSeparatedFromObserverRelation : Bool
    participationSeparatedFromConsentAuthority : Bool
    revisitMultiplicitySeparatedFromIndependence : Bool
    anthropologyRoadmapMethodResidualPaid : Bool
    sourceRoleAndReflexiveProvenanceRetained : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open EthnographyParticipantObservationBoundary public

canonicalEthnographyParticipantObservationBoundary :
  EthnographyParticipantObservationBoundary
canonicalEthnographyParticipantObservationBoundary =
  ethnography-participant-observation-boundary
    true true true true true true true true true true false
