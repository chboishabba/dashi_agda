module DASHI.Wikimedia.IbrahimKnowledgeCoverageRoadmapBrownExtensionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimKnowledgeCoverageRoadmapExact as Roadmap
import DASHI.Wikimedia.IbrahimBrownInstitutionalEpistemicsCrossPollinationExact as Brown

------------------------------------------------------------------------
-- BROWN EXTENSION TO THE IBRAHIM-GUIDED ROADMAP
--
-- The base rank order is unchanged. John/Alice Brown content supplies a new
-- institutional-epistemic operator across the high-flow parent joints rather
-- than another backlog discipline.
------------------------------------------------------------------------

data BrownRoadmapOperator : Set where
  authorityFormationBidirectionality : BrownRoadmapOperator
  coordinateWiseEpistemicAgency : BrownRoadmapOperator
  observerPlurality : BrownRoadmapOperator
  effectiveChoiceContestability : BrownRoadmapOperator
  historicalPowerProvenance : BrownRoadmapOperator

record BrownOperatorRole : Set where
  constructor brown-operator-role
  field
    operator : BrownRoadmapOperator
    sourceSurfaces : String
    appliesToRoadmapSurfaces : String
    lesson : String
    forbiddenPromotion : String
open BrownOperatorRole public

authorityFormationRole : BrownOperatorRole
authorityFormationRole = brown-operator-role authorityFormationBidirectionality
  "JohnAnthonyBrownChildReligiousPowerBidiExact; AliceBrownInstitutionalAgencyChoiceBridgeExact; AliceBrownDissentGovernanceCrossPollinationExact"
  "Place/Country-Community-Knowledge-Authority; Community-Society-SocialScience; State-Politics-Law-Authority"
  "model authority acting on formation/constraint and affected subjects acting back through voice, contestation and revision as separate directed relations"
  "authority asymmetry -> coercion verdict; voice -> automatic justice"

coordinateAgencyRole : BrownOperatorRole
coordinateAgencyRole = brown-operator-role coordinateWiseEpistemicAgency
  "BrownKimberGovernanceProfileBridge; StudentVoiceEpistemicAgencyBridge"
  "Science-Knowledge plurality; Community-Society-SocialScience; State-Politics-Law-Authority"
  "assign epistemic authority by inquiry coordinate: question, projection, relevance, carrier, consumer, dynamics, residual and revision; do not use one scalar participation score"
  "feedback/consultation -> constitutive authority"

observerPluralityRole : BrownOperatorRole
observerPluralityRole = brown-operator-role observerPlurality
  "AliceBrownCorpusLoom; ParentAllyshipMultiObserverBridge; InstitutionalAgencyChoiceBridge"
  "Community-Knowledge; Community-Society; ethnography/participant-observation frontier"
  "subject, parent/community and institution are different observer fibres; disagreement or partial views are retained rather than averaged into one institutional record"
  "parent report -> subject voice; institutional record -> whole-system truth"

effectiveChoiceRole : BrownOperatorRole
effectiveChoiceRole = brown-operator-role effectiveChoiceContestability
  "John formation/exit coordinates; Alice participation/accessibility/contestability coordinates"
  "Community-Knowledge-Authority; State-Politics-Law-Authority; healthcare and education breadth consumers"
  "formal option availability, participation, effective accessibility, refusal, exit and contestability are separate coordinates"
  "formal option -> real agency; participation -> consent"

historicalPowerRole : BrownOperatorRole
historicalPowerRole = brown-operator-role historicalPowerProvenance
  "John colonial-dispossession research-question lane; Alice situated observer/agency lane; Country/Mabo provenance owners"
  "Place/Country-Community-Knowledge-Authority; archaeology/ethnography frontier"
  "historical comparison must carry source/community/observer provenance and may expose structural analogy without identifying histories"
  "colonial comparison -> identical history; institutional classification -> community authority"

------------------------------------------------------------------------
-- The first four ranked parent joints now inherit this operator family.
------------------------------------------------------------------------

record BrownRoadmapApplication : Set where
  constructor brown-roadmap-application
  field
    placeCommunityKnowledgeAuthorityGetsBrownOperator : Bool
    scienceKnowledgePluralityGetsCoordinateAgency : Bool
    communitySocietyGetsObserverPlurality : Bool
    statePoliticsLawGetsAuthorityContestability : Bool
    archaeologyGetsHistoricalPowerProvenanceLater : Bool
    baseRankOrderChanged : Bool
open BrownRoadmapApplication public

canonicalBrownRoadmapApplication : BrownRoadmapApplication
canonicalBrownRoadmapApplication = brown-roadmap-application
  true true true true true false

basePriorityOne : Roadmap.RoadmapLeaf
basePriorityOne = Roadmap.placeCommunityKnowledgeAuthority

basePriorityTwo : Roadmap.RoadmapLeaf
basePriorityTwo = Roadmap.scienceKnowledgePlurality

basePriorityThree : Roadmap.RoadmapLeaf
basePriorityThree = Roadmap.communitySocietySocialScience

basePriorityFour : Roadmap.RoadmapLeaf
basePriorityFour = Roadmap.statePoliticsLawAuthority

brownCrossBoundary : Brown.BrownInstitutionalEpistemicsBoundary
brownCrossBoundary = Brown.canonicalBrownInstitutionalEpistemicsBoundary

------------------------------------------------------------------------
-- Cross-tranche policy.
------------------------------------------------------------------------

record BrownExtendedRoadmapPolicy : Set where
  constructor brown-extended-roadmap-policy
  field
    affectedVoiceIsNecessaryCoordinateWhenRelevant : Bool
    affectedVoiceIsAutomaticallySufficient : Bool
    authorityMustBeCoordinateSpecific : Bool
    observerIdentityMustBeRetained : Bool
    effectiveChoiceDistinctFromFormalAvailability : Bool
    sourceFamilyAnalogyCreatesEvidence : Bool
    historicalAnalogyCreatesIdentity : Bool
    communityAuthorityMayDescendFromInstitutionalRecognition : Bool
open BrownExtendedRoadmapPolicy public

canonicalBrownExtendedRoadmapPolicy : BrownExtendedRoadmapPolicy
canonicalBrownExtendedRoadmapPolicy =
  brown-extended-roadmap-policy true false true true true false false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ParticipationEqualsAgency : Set where
data VoiceEqualsMetaRuleAuthority : Set where
data InstitutionRecordEqualsCommunityKnowledge : Set where
data FormalAvailabilityEqualsEffectiveChoice : Set where
data SharedInstitutionalPatternEqualsSharedEmpiricalHistory : Set where

participationStillNotAgency : ParticipationEqualsAgency → ⊥
participationStillNotAgency ()

voiceStillNotMetaRuleAuthority : VoiceEqualsMetaRuleAuthority → ⊥
voiceStillNotMetaRuleAuthority ()

institutionRecordStillNotCommunityKnowledge : InstitutionRecordEqualsCommunityKnowledge → ⊥
institutionRecordStillNotCommunityKnowledge ()

formalAvailabilityStillNotEffectiveChoice : FormalAvailabilityEqualsEffectiveChoice → ⊥
formalAvailabilityStillNotEffectiveChoice ()

sharedPatternStillNotSharedHistory : SharedInstitutionalPatternEqualsSharedEmpiricalHistory → ⊥
sharedPatternStillNotSharedHistory ()
