module DASHI.Wikimedia.IbrahimSnowballRitualMythCommunityInstitutionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballReligionEschatologyIdeologyIdentityExact as Prior
import DASHI.Wikimedia.IbrahimSnowballCommunitySocietySocialScienceExact as Social
import DASHI.Culture.WitchSelfIdentificationPredicateUseBidiExact as Witch
import DASHI.Reasoning.TypedMemeCompiler as Meme

------------------------------------------------------------------------
-- IBRAHIM / SNOWBALL CONTINUATION:
-- RELIGION <-> CULTURE <-> RITUAL <-> MYTH/NARRATIVE <-> COMMUNITY <->
-- INSTITUTION, with IDEOLOGY <-> POLITICAL MOVEMENT <-> STATE as a parallel
-- mobilisation branch.
--
-- External identities checked 2026-09-10:
--   ritual             Q189819
--   myth               Q12827256
--   mythology          Q9134
--   political movement Q2738074
--   institution        Q178706
--   community          Q177634 (reused existing high-flow identity)
--
-- These are identity/navigation coordinates only.  They do not establish
-- ritual meaning, sacred truth, community authority, institutional legitimacy,
-- movement membership, political causation, or empirical truth.
------------------------------------------------------------------------

ritualQid : Identity.ExternalIdentityDemand
ritualQid = Identity.mkOptionalIdentityDemand
  "Ibrahim ritual/myth/community snowball" "external concept identity" "ritual"
  Identity.wikidataQid
  (Identity.verified "Q189819" "Wikidata item checked 2026-09-10; activities performed according to a set sequence")

mythQid : Identity.ExternalIdentityDemand
mythQid = Identity.mkOptionalIdentityDemand
  "Ibrahim ritual/myth/community snowball" "external concept identity" "myth"
  Identity.wikidataQid
  (Identity.verified "Q12827256" "Wikidata item checked 2026-09-10; traditional narrative identity only")

mythologyQid : Identity.ExternalIdentityDemand
mythologyQid = Identity.mkOptionalIdentityDemand
  "Ibrahim ritual/myth/community snowball" "external concept identity" "mythology"
  Identity.wikidataQid
  (Identity.verified "Q9134" "Wikidata item checked 2026-09-10")

politicalMovementQid : Identity.ExternalIdentityDemand
politicalMovementQid = Identity.mkOptionalIdentityDemand
  "Ibrahim ritual/myth/community snowball" "external concept identity" "political movement"
  Identity.wikidataQid
  (Identity.verified "Q2738074" "Wikidata item checked 2026-09-10")

institutionQid : Identity.ExternalIdentityDemand
institutionQid = Identity.mkOptionalIdentityDemand
  "Ibrahim ritual/myth/community snowball" "external concept identity" "institution"
  Identity.wikidataQid
  (Identity.verified "Q178706" "Wikidata item checked 2026-09-10")

communityQid : Identity.ExternalIdentityDemand
communityQid = Identity.mkOptionalIdentityDemand
  "Ibrahim ritual/myth/community snowball" "external concept identity" "community"
  Identity.wikidataQid
  (Identity.verified "Q177634" "existing DASHI high-flow Wikidata identity reused")

------------------------------------------------------------------------
-- Navigation roles.  The names here are local graph probes, not a universal
-- ontology and not statements that one node is the unique parent of another.
------------------------------------------------------------------------

data RitualMythGraphNode : Set where
  ritualNode mythNode mythologyNode communityNode institutionNode politicalMovementNode :
    RitualMythGraphNode

record RitualMythNodeAudit : Set where
  constructor ritual-myth-node-audit
  field
    node : RitualMythGraphNode
    externalRole : String
    dashiSubstrate : String
    principalNoncollapse : String
    attributionRequired : Bool
    twoEyedComparisonRequired : Bool
    currentDescriptionDefinesDashiOntology : Bool
open RitualMythNodeAudit public

ritualAudit : RitualMythNodeAudit
ritualAudit = ritual-myth-node-audit ritualNode
  "structured/repeated activity; may be religious, social, political, domestic or otherwise situated"
  "WitchSelfIdentificationPredicateUseBidiExact; Country/LES ritual-knowledge lanes; cuisine/ritual-memory; authority gates"
  "visible sequence != meaning != consent != community authority != metaphysical truth"
  true true false

mythAudit : RitualMythNodeAudit
mythAudit = ritual-myth-node-audit mythNode
  "traditional narrative identity/navigation coordinate"
  "TypedMemeCompiler; political-theology narrative atlas; history/culture provenance owners"
  "myth/narrative role != empirical falsehood; myth may propose an interpretation but cannot pay proof"
  true true false

mythologyAudit : RitualMythNodeAudit
mythologyAudit = ritual-myth-node-audit mythologyNode
  "collection/system of myths and sacred/traditional narratives"
  "culture/history/religion/political-theology and source genealogy owners"
  "shared mythology label does not determine literalism, doctrine, identity, ritual, institution or political use"
  true true false

communityAudit : RitualMythNodeAudit
communityAudit = ritual-myth-node-audit communityNode
  "situated social unit / membership / shared practice navigation coordinate"
  "Community high-flow owner; Two-Eyed/Country; Alice Brown voice/agency; culture membership boundaries"
  "community observation/practice != authority to define all members and != whole society"
  true true false

institutionAudit : RitualMythNodeAudit
institutionAudit = ritual-myth-node-audit institutionNode
  "institutionalised rule/role/organisation surface"
  "Brown institutional agency; governance; religious-authority and authority-nonpromotion owners"
  "institutional record/classification/ritual != community assent, self-description or complete social meaning"
  true true false

politicalMovementAudit : RitualMythNodeAudit
politicalMovementAudit = ritual-myth-node-audit politicalMovementNode
  "collective political-goal/mobilisation coordinate"
  "ideology/political-theology, governance, state/politics and social-movement-adjacent owners"
  "ideology != movement membership != movement organisation != State authority"
  true true false

------------------------------------------------------------------------
-- Regression 1: the same observable ritual sequence can carry distinct
-- authority/meaning relations.  Sequence alone cannot answer that consumer.
------------------------------------------------------------------------

data RitualSituatedCase : Set where
  sameSequenceCommunityAuthorised : RitualSituatedCase
  sameSequenceExternallyInstitutionalised : RitualSituatedCase

data RitualSurface : Set where sameRitualSequence : RitualSurface
data RitualAuthorityReading : Set where
  communityAuthorisedReading : RitualAuthorityReading
  externallyInstitutionalisedReading : RitualAuthorityReading

ritualSurface : RitualSituatedCase → RitualSurface
ritualSurface _ = sameRitualSequence

ritualAuthorityReading : RitualSituatedCase → RitualAuthorityReading
ritualAuthorityReading sameSequenceCommunityAuthorised = communityAuthorisedReading
ritualAuthorityReading sameSequenceExternallyInstitutionalised = externallyInstitutionalisedReading

ritualAuthorityDefect : INF.NonFactorabilityWitness ritualSurface ritualAuthorityReading
ritualAuthorityDefect = INF.nonFactorabilityWitness
  sameSequenceCommunityAuthorised sameSequenceExternallyInstitutionalised refl (λ ())

ritualSequenceCannotFactorAuthorityMeaning :
  INF.FactorsThrough ritualSurface ritualAuthorityReading → ⊥
ritualSequenceCannotFactorAuthorityMeaning =
  INF.witnessRulesOutEveryFlatFactorisation ritualAuthorityDefect

------------------------------------------------------------------------
-- Regression 2: the same narrative surface can inhabit different roles.
-- Narrative identity alone therefore cannot answer historical/theological/
-- political/literary-use consumers.
------------------------------------------------------------------------

data NarrativeSituatedCase : Set where
  sameNarrativeSacredMythicUse : NarrativeSituatedCase
  sameNarrativePoliticalMobilisationUse : NarrativeSituatedCase

data NarrativeSurface : Set where sameNarrativeToken : NarrativeSurface
data NarrativeRoleReading : Set where
  sacredMythicRole : NarrativeRoleReading
  politicalMobilisationRole : NarrativeRoleReading

narrativeSurface : NarrativeSituatedCase → NarrativeSurface
narrativeSurface _ = sameNarrativeToken

narrativeRole : NarrativeSituatedCase → NarrativeRoleReading
narrativeRole sameNarrativeSacredMythicUse = sacredMythicRole
narrativeRole sameNarrativePoliticalMobilisationUse = politicalMobilisationRole

narrativeRoleDefect : INF.NonFactorabilityWitness narrativeSurface narrativeRole
narrativeRoleDefect = INF.nonFactorabilityWitness
  sameNarrativeSacredMythicUse sameNarrativePoliticalMobilisationUse refl (λ ())

narrativeSurfaceCannotFactorRole :
  INF.FactorsThrough narrativeSurface narrativeRole → ⊥
narrativeSurfaceCannotFactorRole =
  INF.witnessRulesOutEveryFlatFactorisation narrativeRoleDefect

------------------------------------------------------------------------
-- Regression 3: an ideology label cannot recover whether/how a political
-- movement is institutionally related to State authority.
------------------------------------------------------------------------

data IdeologyMovementCase : Set where
  sameIdeologyNonStateMovement : IdeologyMovementCase
  sameIdeologyStateInstitutionalised : IdeologyMovementCase

data IdeologySurface : Set where sameIdeologyLabel : IdeologySurface
data StateRelationReading : Set where
  nonStateMovementRelation : StateRelationReading
  stateInstitutionalRelation : StateRelationReading

ideologySurface : IdeologyMovementCase → IdeologySurface
ideologySurface _ = sameIdeologyLabel

stateRelation : IdeologyMovementCase → StateRelationReading
stateRelation sameIdeologyNonStateMovement = nonStateMovementRelation
stateRelation sameIdeologyStateInstitutionalised = stateInstitutionalRelation

ideologyStateRelationDefect : INF.NonFactorabilityWitness ideologySurface stateRelation
ideologyStateRelationDefect = INF.nonFactorabilityWitness
  sameIdeologyNonStateMovement sameIdeologyStateInstitutionalised refl (λ ())

ideologyCannotFactorMovementStateRelation :
  INF.FactorsThrough ideologySurface stateRelation → ⊥
ideologyCannotFactorMovementStateRelation =
  INF.witnessRulesOutEveryFlatFactorisation ideologyStateRelationDefect

------------------------------------------------------------------------
-- Existing source-bound regressions are reused rather than restated as prose.
------------------------------------------------------------------------

witchSentenceUseBoundary : INF.FactorsThrough Witch.witchSentence Witch.witchUse → ⊥
witchSentenceUseBoundary = Witch.sameSentenceCannotRecoverUse

memeAuthorityBoundary : Meme.TypedMemeCompilerAuthorityBoundary
memeAuthorityBoundary = Meme.canonicalTypedMemeCompilerAuthorityBoundary

priorReligionBoundary : Prior.ReligionEschatologyIdeologySnowballBoundary
priorReligionBoundary = Prior.canonicalReligionEschatologyIdeologySnowballBoundary

socialFunnelBoundary : Social.SocialFunnelSnowballPayment
socialFunnelBoundary = Social.currentSocialFunnelPayment

------------------------------------------------------------------------
-- Snowball result. Current named coordinates are examples discovered at this
-- graph seam; a later consumer can add further axes without changing the
-- abstract invariant.
------------------------------------------------------------------------

record RitualMythCommunityInstitutionBoundary : Set where
  constructor ritual-myth-community-institution-boundary
  field
    qidsAttachedWhenSafelyResolvable : Bool
    ritualSequenceDoesNotDetermineMeaning : Bool
    ritualSequenceDoesNotDetermineAuthority : Bool
    mythMayProposeButCannotProve : Bool
    mythLabelDoesNotMeanEmpiricallyFalse : Bool
    narrativeRoleRetainsSourceAndContext : Bool
    institutionDoesNotCreateCommunityAuthority : Bool
    communityPracticeDoesNotDefineWholeReligion : Bool
    organisedInstitutionDoesNotExhaustReligion : Bool
    ideologyDoesNotEqualPoliticalMovement : Bool
    politicalMovementDoesNotEqualState : Bool
    twoEyedEmicEticComparisonRetained : Bool
    currentAxisVocabularyClaimedComplete : Bool
open RitualMythCommunityInstitutionBoundary public

canonicalRitualMythCommunityInstitutionBoundary :
  RitualMythCommunityInstitutionBoundary
canonicalRitualMythCommunityInstitutionBoundary =
  ritual-myth-community-institution-boundary
    true true true true true true true true true true true true false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data RitualSequenceCreatesConsentOrAuthority : Set where
data RitualCreatesReligiousTruth : Set where
data MythLabelCreatesEmpiricalFalsehood : Set where
data MythCreatesHistoricalFact : Set where
data InstitutionCreatesCommunityAuthority : Set where
data ReligiousInstitutionDefinesEveryMember : Set where
data IdeologyCreatesPoliticalMovementMembership : Set where
data PoliticalMovementCreatesStateAuthority : Set where
data QidCreatesRitualOrMythTruth : Set where

ritualSequenceDoesNotCreateConsentOrAuthority : RitualSequenceCreatesConsentOrAuthority → ⊥
ritualSequenceDoesNotCreateConsentOrAuthority ()

ritualDoesNotCreateReligiousTruth : RitualCreatesReligiousTruth → ⊥
ritualDoesNotCreateReligiousTruth ()

mythLabelDoesNotCreateEmpiricalFalsehood : MythLabelCreatesEmpiricalFalsehood → ⊥
mythLabelDoesNotCreateEmpiricalFalsehood ()

mythDoesNotCreateHistoricalFact : MythCreatesHistoricalFact → ⊥
mythDoesNotCreateHistoricalFact ()

institutionDoesNotCreateCommunityAuthority : InstitutionCreatesCommunityAuthority → ⊥
institutionDoesNotCreateCommunityAuthority ()

religiousInstitutionDoesNotDefineEveryMember : ReligiousInstitutionDefinesEveryMember → ⊥
religiousInstitutionDoesNotDefineEveryMember ()

ideologyDoesNotCreateMovementMembership : IdeologyCreatesPoliticalMovementMembership → ⊥
ideologyDoesNotCreateMovementMembership ()

politicalMovementDoesNotCreateStateAuthority : PoliticalMovementCreatesStateAuthority → ⊥
politicalMovementDoesNotCreateStateAuthority ()

qidDoesNotCreateRitualOrMythTruth : QidCreatesRitualOrMythTruth → ⊥
qidDoesNotCreateRitualOrMythTruth ()
