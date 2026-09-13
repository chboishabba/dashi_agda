module DASHI.Wikimedia.IbrahimSnowballCommunitySocietySocialScienceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.SnowballPluralLensInvariantExact as Snowball
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.IbrahimEnglishCommunityStateScienceParentBridgeExact as HighFlow
import DASHI.Wikimedia.IbrahimEnglishSocialScienceFunnelBridgeExact as SocialScience

------------------------------------------------------------------------
-- IBRAHIM SNOWBALL WALK: COMMUNITY -> SOCIETY -> SOCIAL SCIENCE
--
-- Ibrahim, Danforth, Dodds (2017), Journal of Computational Science 19, 21-30,
-- DOI 10.1016/j.jocs.2016.12.001, is retained only as an external navigation
-- prior.  Current EN observations inspected 2026-09-10 are revision-sensitive:
--   * Community is presented as a social unit with shared significant
--     characteristics, place/practice/identity and institutional relations;
--   * Society is presented as persistent social interaction / social relations,
--     commonly involving territory, institutions, culture and political
--     authority;
--   * Social science is presented as a branch of science studying societies and
--     relationships, with plural quantitative/positivist and interpretive
--     methodologies.
--
-- Those observations nominate a seam. They do not determine DASHI ontology,
-- prove aggregation validity, create community authority, or erase source role.
------------------------------------------------------------------------

ibrahimSource : Attribution.AttributedSource
ibrahimSource = Attribution.mkDOISource
  "Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds"
  "Connecting every bit of knowledge: The structure of Wikipedia's First Link Network"
  "Journal of Computational Science 19, 21-30"
  "2017"
  "10.1016/j.jocs.2016.12.001"
  "https://doi.org/10.1016/j.jocs.2016.12.001"
  Attribution.academicArticleSource
  "external traversal-funnel/navigation prior only; does not pay DASHI semantic, empirical, legal, cultural or community authority"
  Attribution.publicAttribution

record SnowballFunnelObservation : Set where
  constructor snowball-funnel-observation
  field
    child : String
    candidateParent : String
    observationDate : String
    sourceRole : String
    revisionSensitive : Bool
    parentIsProofDependency : Bool
    attributionMustSurvive : Bool
    twoEyedComparisonRequired : Bool
    presentAxisVocabularyClaimedComplete : Bool
open SnowballFunnelObservation public

communitySocietyObservation : SnowballFunnelObservation
communitySocietyObservation = snowball-funnel-observation
  "Community"
  "Society / social relations / institutions (candidate consolidation seam, not a literal timeless first-link theorem)"
  "2026-09-10"
  "current EN navigation observation compared against Ibrahim high-flow prior"
  true false true true false

societySocialScienceObservation : SnowballFunnelObservation
societySocialScienceObservation = snowball-funnel-observation
  "Society"
  "Social science / sociology / social inquiry"
  "2026-09-10"
  "current EN discipline/navigation observation; external only"
  true false true true false

------------------------------------------------------------------------
-- Finite specimen of axes discovered at this seam.  This list is deliberately
-- NOT the invariant and is not claimed complete.  It witnesses how a local
-- consumer can instantiate the abstract plural lens and later snowball more.
------------------------------------------------------------------------

data LocalSocialAxis : Set where
  communityIdentityAxis : LocalSocialAxis
  placeRelationAxis : LocalSocialAxis
  institutionAxis : LocalSocialAxis
  affectedVoiceAxis : LocalSocialAxis
  authorityAxis : LocalSocialAxis
  observerAxis : LocalSocialAxis
  methodAxis : LocalSocialAxis
  historicalRelationAxis : LocalSocialAxis
  sourceRoleAxis : LocalSocialAxis

allRelevant : LocalSocialAxis → Bool
allRelevant axis = true

allRetained : LocalSocialAxis → Bool
allRetained axis = true

localSocialLens : Snowball.PluralLens LocalSocialAxis
localSocialLens = Snowball.plural-lens allRelevant allRetained (λ axis proof → refl)

record LocalLensWitness : Set where
  constructor local-lens-witness
  field
    lens : Snowball.PluralLens LocalSocialAxis
    axesAreConsumerLocalWitnesses : Bool
    newAxesMaySnowball : Bool
    currentListIsCompleteOntology : Bool
open LocalLensWitness public

communitySocietyLensWitness : LocalLensWitness
communitySocietyLensWitness = local-lens-witness localSocialLens true true false

------------------------------------------------------------------------
-- Exact non-factorability regression.
-- The same coarse society-level surface can coexist with distinct community
-- authority/voice states.  Therefore a society summary cannot answer every
-- community-authority query merely because both states aggregate to "society".
------------------------------------------------------------------------

data SituatedSocialState : Set where
  sameSocietyCommunityVoiceExcluded : SituatedSocialState
  sameSocietyCommunityVoiceConstitutive : SituatedSocialState

data SocietySurface : Set where
  sameSocietySurface : SocietySurface

data CommunityAuthorityAnswer : Set where
  affectedVoiceNotConstitutive : CommunityAuthorityAnswer
  affectedVoiceConstitutive : CommunityAuthorityAnswer

societyProjection : SituatedSocialState → SocietySurface
societyProjection state = sameSocietySurface

communityAuthorityAnswer : SituatedSocialState → CommunityAuthorityAnswer
communityAuthorityAnswer sameSocietyCommunityVoiceExcluded = affectedVoiceNotConstitutive
communityAuthorityAnswer sameSocietyCommunityVoiceConstitutive = affectedVoiceConstitutive

societySurfaceAuthorityDefect :
  INF.NonFactorabilityWitness societyProjection communityAuthorityAnswer
societySurfaceAuthorityDefect = INF.nonFactorabilityWitness
  sameSocietyCommunityVoiceExcluded
  sameSocietyCommunityVoiceConstitutive
  refl
  (λ ())

societySurfaceCannotFactorEveryCommunityAuthorityQuery :
  INF.FactorsThrough societyProjection communityAuthorityAnswer → ⊥
societySurfaceCannotFactorEveryCommunityAuthorityQuery =
  INF.witnessRulesOutEveryFlatFactorisation societySurfaceAuthorityDefect

------------------------------------------------------------------------
-- Two-Eyed / attribution snowball reading.
-- "Two-Eyed" is used as a cross-pollinated discipline: coordinate distinct
-- knowledge histories/observer positions without synthesising or ranking them
-- by default.  Wikipedia is one external navigation eye; DASHI/source-bounded
-- community, institutional, scientific, historical and affected-subject fibres
-- are not replaced by it.
------------------------------------------------------------------------

record SocialFunnelSnowballPayment : Set where
  constructor social-funnel-snowball-payment
  field
    reusesCommunityHighFlowOwner : Bool
    reusesSocialScienceOwner : Bool
    externalPriorAttributed : Bool
    currentWikipediaRevisionBounded : Bool
    communityAndSocietyNotIdentified : Bool
    societyAndStateNotIdentified : Bool
    oneCommunityNotPromotedToWholeSociety : Bool
    oneInstitutionNotPromotedToWholeSociety : Bool
    oneMethodNotPromotedToAllSocialScience : Bool
    affectedVoiceNotReplacedByInstitutionalRecord : Bool
    missingRelevantAxisForcesReopening : Bool
    newAxisMaySnowballWithoutGlobalOntologyRewrite : Bool
    presentAxisListClaimedComplete : Bool
open SocialFunnelSnowballPayment public

currentSocialFunnelPayment : SocialFunnelSnowballPayment
currentSocialFunnelPayment = social-funnel-snowball-payment
  true true true true true true true true true true true true false

------------------------------------------------------------------------
-- Next graph frontier discovered by this payment.
-- These are traversal candidates, not declarations of missing theory.
-- Knowledge is broad and already strong; Culture and History are also rich in
-- DASHI but need parent/aggregation audits under the same snowball discipline.
------------------------------------------------------------------------

data NextFunnelNode : Set where
  knowledgeNode : NextFunnelNode
  cultureNode : NextFunnelNode
  historyNode : NextFunnelNode
  polityStateNode : NextFunnelNode
  anthropologyArchaeologyNode : NextFunnelNode

record NextSnowballProbe : Set where
  constructor next-snowball-probe
  field
    node : NextFunnelNode
    externalReason : String
    dashiReading : String
    snowballQuestion : String
    leafAbsenceAlreadyProven : Bool
open NextSnowballProbe public

knowledgeProbe : NextSnowballProbe
knowledgeProbe = next-snowball-probe knowledgeNode
  "Ibrahim high-flow Science seam and current EN Science/Knowledge relation"
  "strong plural-knowledge, source, proof, scientific and Indigenous/community substrate"
  "which knowledge role/source/authority distinctions must survive each consumer projection?"
  false

cultureProbe : NextSnowballProbe
cultureProbe = next-snowball-probe cultureNode
  "Community and Society descriptions both expose culture as a connective coordinate"
  "large Culture/Indigenous/feminist/dialectical/philosophical substrate already present"
  "where does a shared cultural label fail to factor provenance, grammar, authority or historical relation?"
  false

historyProbe : NextSnowballProbe
historyProbe = next-snowball-probe historyNode
  "Social science currently enumerates history; current History page explicitly separates past events from representations of the past"
  "strong historical/source/provenance and deep-time material, but no assumption of one universal history projection"
  "which event/source/narrative/observer/history distinctions are erased by a parent summary?"
  false

polityStateProbe : NextSnowballProbe
polityStateProbe = next-snowball-probe polityStateNode
  "Ibrahim identifies State as a high-flow funnel; current state definitions relate society, territory, governance and recognition"
  "Governance/SensibLaw/Mabo/Country/political-economy substrate strong"
  "which recognition, sovereignty, Country/community authority and institutional-power axes fail to factor through State?"
  false

anthropologyArchaeologyProbe : NextSnowballProbe
anthropologyArchaeologyProbe = next-snowball-probe anthropologyArchaeologyNode
  "Social science currently enumerates anthropology and archaeology"
  "anthropology recently gained method/discipline owners; archaeology remains a thinner substantive-method lane"
  "which material-context, provenance, chronology, community-authority and interpretation axes must snowball before aggregation?"
  false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data IbrahimFlowCreatesAuthority : Set where
data SocietySummaryCreatesCommunityAuthority : Set where
data SocialScienceParentMakesMethodsEquivalent : Set where
data TwoEyedMeansWikipediaPlusDashiAreEpistemicallyEquivalent : Set where
data CurrentAxisListIsUniversalSocialOntology : Set where

ibrahimFlowDoesNotCreateAuthority : IbrahimFlowCreatesAuthority → ⊥
ibrahimFlowDoesNotCreateAuthority ()

societySummaryDoesNotCreateCommunityAuthority : SocietySummaryCreatesCommunityAuthority → ⊥
societySummaryDoesNotCreateCommunityAuthority ()

socialScienceParentDoesNotMakeMethodsEquivalent : SocialScienceParentMakesMethodsEquivalent → ⊥
socialScienceParentDoesNotMakeMethodsEquivalent ()

twoEyedDoesNotMakeSourcesEquivalent :
  TwoEyedMeansWikipediaPlusDashiAreEpistemicallyEquivalent → ⊥
twoEyedDoesNotMakeSourcesEquivalent ()

finiteAxisSpecimenIsNotUniversalOntology : CurrentAxisListIsUniversalSocialOntology → ⊥
finiteAxisSpecimenIsNotUniversalOntology ()

communityHighFlowReceipt : HighFlow.CommunityBridgeRequirements
communityHighFlowReceipt = HighFlow.communityRequirements

socialScienceBoundary : SocialScience.SocialScienceFunnelBoundary
socialScienceBoundary = SocialScience.canonicalSocialScienceFunnelBoundary
