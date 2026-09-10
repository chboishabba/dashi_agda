module DASHI.Wikimedia.IbrahimSnowballChildhoodCategorisationConformityPsychologyBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.CategoryAuthorityAuditExact as Category
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Discovery
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballKinshipSocialisationEducationAuthorityBidiExact as Prior
import DASHI.Culture.JaneElliottBlueEyesBrownEyesPluralLensExact as Elliott
import DASHI.Culture.JaneElliottAliceBrownEpistemicAgencyCrossPollinationExact as ElliottAlice

------------------------------------------------------------------------
-- IBRAHIM / SNOWBALL BIDI CONTINUATION:
--
--   childhood / child development
--        <-> categorisation / discipline
--        <-> peer-group conformity / authority obedience
--        <-> social psychology
--        <-> ethics / experimental design
--
-- External graph/QID structure is a navigation and attribution prior only.
-- Concrete DASHI counterexamples constrain the parent concepts in return.
--
-- External identities checked 2026-09-10:
--   childhood          Q276258
--   child development  Q407784
--   social psychology  Q161272
--   conformity         Q221284
--   obedience          Q1456974
--   child discipline   Q933555
--   ethics             Q9465
--
-- The exact broad `categorisation` concept identity is deliberately left
-- unresolved here rather than promoting a nearby item.
------------------------------------------------------------------------

childhoodQid : Identity.ExternalIdentityDemand
childhoodQid = Identity.mkOptionalIdentityDemand
  "Ibrahim childhood/social-psychology BIDI" "external concept identity"
  "childhood" Identity.wikidataQid
  (Identity.verified "Q276258" "Wikidata identity checked 2026-09-10")

childDevelopmentQid : Identity.ExternalIdentityDemand
childDevelopmentQid = Identity.mkOptionalIdentityDemand
  "Ibrahim childhood/social-psychology BIDI" "external concept identity"
  "child development" Identity.wikidataQid
  (Identity.verified "Q407784" "Wikidata identity checked 2026-09-10")

socialPsychologyQid : Identity.ExternalIdentityDemand
socialPsychologyQid = Identity.mkOptionalIdentityDemand
  "Ibrahim childhood/social-psychology BIDI" "external discipline identity"
  "social psychology" Identity.wikidataQid
  (Identity.verified "Q161272" "Wikidata identity checked 2026-09-10")

conformityQid : Identity.ExternalIdentityDemand
conformityQid = Identity.mkOptionalIdentityDemand
  "Ibrahim childhood/social-psychology BIDI" "external concept identity"
  "conformity" Identity.wikidataQid
  (Identity.verified "Q221284" "Wikidata identity checked 2026-09-10; kept distinct from obedience")

obedienceQid : Identity.ExternalIdentityDemand
obedienceQid = Identity.mkOptionalIdentityDemand
  "Ibrahim childhood/social-psychology BIDI" "external concept identity"
  "obedience" Identity.wikidataQid
  (Identity.verified "Q1456974" "Wikidata identity checked 2026-09-10; yielding to instructions from authority is a distinct role")

childDisciplineQid : Identity.ExternalIdentityDemand
childDisciplineQid = Identity.mkOptionalIdentityDemand
  "Ibrahim childhood/social-psychology BIDI" "external concept identity"
  "child discipline" Identity.wikidataQid
  (Identity.verified "Q933555" "Wikidata identity checked 2026-09-10")

ethicsQid : Identity.ExternalIdentityDemand
ethicsQid = Identity.mkOptionalIdentityDemand
  "Ibrahim childhood/social-psychology BIDI" "external discipline/concept identity"
  "ethics" Identity.wikidataQid
  (Identity.verified "Q9465" "Wikidata identity checked 2026-09-10")

categorisationQid : Identity.ExternalIdentityDemand
categorisationQid = Identity.mkOptionalIdentityDemand
  "Ibrahim childhood/social-psychology BIDI" "external concept identity"
  "categorisation / classification as social-cognitive process" Identity.wikidataQid
  (Identity.unresolved "exact broad concept QID not safely resolved; nearby classification/category items are not promoted")

------------------------------------------------------------------------
-- BIDI graph audits. Parent nodes nominate search obligations; child-level
-- counterexamples can force the parent interpretation to become richer.
------------------------------------------------------------------------

data ChildSocialGraphNode : Set where
  childhoodNode childDevelopmentNode categorisationNode disciplineNode
  conformityNode obedienceNode socialPsychologyNode ethicsNode : ChildSocialGraphNode

record ChildSocialGraphAudit : Set where
  constructor child-social-graph-audit
  field
    node : ChildSocialGraphNode
    upwardReading : String
    downwardConstraint : String
    principalWrongTypeRisk : String
    attributionRequired : Bool
    twoEyedRequired : Bool
    parentLabelExplainsEveryCase : Bool
open ChildSocialGraphAudit public

conformityAudit : ChildSocialGraphAudit
conformityAudit = child-social-graph-audit conformityNode
  "group-norm / peer-influence navigation coordinate within social psychology"
  "same visible compliant behaviour may arise through peer conformity, authority obedience, strategic compliance, coercion or autonomous agreement"
  "conformity != obedience != assent != private belief"
  true true false

obedienceAudit : ChildSocialGraphAudit
obedienceAudit = child-social-graph-audit obedienceNode
  "authority-instruction response coordinate"
  "authority-following surface does not establish legitimacy, consent, endorsement, or voluntariness"
  "obedience != legitimate authority != autonomous endorsement"
  true true false

categorisationAudit : ChildSocialGraphAudit
categorisationAudit = child-social-graph-audit categorisationNode
  "classification/categorisation candidate joining cognition, social identity, education and institutional power"
  "Elliott demonstrates that assigned category plus authority/treatment can alter the social situation without making the category a natural identity truth"
  "assigned classifier != intrinsic identity != neutral category genesis"
  true true false

ethicsAudit : ChildSocialGraphAudit
ethicsAudit = child-social-graph-audit ethicsNode
  "normative/experimental-governance consumer adjacent to child research and intervention"
  "measured effect, social-psychology result or pedagogical objective does not itself settle consent, safeguards, proportionality, debriefing or downstream use"
  "empirical effectiveness != ethical permissibility"
  true true false

------------------------------------------------------------------------
-- Exact regression 1: one visible compliance surface cannot recover whether
-- the mechanism/relationship is peer conformity or authority obedience.
------------------------------------------------------------------------

data ComplianceCase : Set where
  sameBehaviourPeerConformity sameBehaviourAuthorityObedience : ComplianceCase

data ComplianceSurface : Set where sameVisibleCompliance : ComplianceSurface
data ComplianceRelation : Set where peerNormRelation authorityInstructionRelation : ComplianceRelation

complianceSurface : ComplianceCase → ComplianceSurface
complianceSurface _ = sameVisibleCompliance

complianceRelation : ComplianceCase → ComplianceRelation
complianceRelation sameBehaviourPeerConformity = peerNormRelation
complianceRelation sameBehaviourAuthorityObedience = authorityInstructionRelation

complianceRelationDefect : INF.NonFactorabilityWitness complianceSurface complianceRelation
complianceRelationDefect = INF.nonFactorabilityWitness
  sameBehaviourPeerConformity sameBehaviourAuthorityObedience refl (λ ())

visibleComplianceCannotFactorRelation :
  INF.FactorsThrough complianceSurface complianceRelation → ⊥
visibleComplianceCannotFactorRelation =
  INF.witnessRulesOutEveryFlatFactorisation complianceRelationDefect

------------------------------------------------------------------------
-- Exact regression 2: externally assigned category cannot recover the relevant
-- power/treatment relation. Reuse Elliott's concrete nonfactorability witness.
------------------------------------------------------------------------

assignedCategoryCannotFactorPowerRelation :
  INF.FactorsThrough Elliott.groupObserver Elliott.constraintOutcome → ⊥
assignedCategoryCannotFactorPowerRelation = Elliott.groupCannotRecoverPowerRelation

elliottAliceContestabilityBoundary :
  INF.FactorsThrough ElliottAlice.surfaceObservation ElliottAlice.contestabilityAnswer → ⊥
elliottAliceContestabilityBoundary = ElliottAlice.surfaceCannotRecoverContestability

------------------------------------------------------------------------
-- Category-genesis and snowball-discovery owners constrain the graph globally.
------------------------------------------------------------------------

categoryAuthorityBoundary : Category.CategoryAuthorityBoundary
categoryAuthorityBoundary = Category.canonicalCategoryAuthorityBoundary

discoveryBoundary : Discovery.SnowballDiscoveryBoundary
discoveryBoundary = Discovery.canonicalSnowballDiscoveryBoundary

data VisibleConformityCreatesAssent : Set where
data ObedienceCreatesLegitimateAuthority : Set where
data AssignedCategoryCreatesIdentityTruth : Set where
data ChildDisciplineCreatesEthicalLegitimacy : Set where
data ExperimentalEffectSettlesEthics : Set where
data SocialPsychologyParentErasesParticipantVoice : Set where

visibleConformityDoesNotCreateAssent : VisibleConformityCreatesAssent → ⊥
visibleConformityDoesNotCreateAssent ()

obedienceDoesNotCreateLegitimateAuthority : ObedienceCreatesLegitimateAuthority → ⊥
obedienceDoesNotCreateLegitimateAuthority ()

assignedCategoryDoesNotCreateIdentityTruth : AssignedCategoryCreatesIdentityTruth → ⊥
assignedCategoryDoesNotCreateIdentityTruth ()

childDisciplineDoesNotCreateEthicalLegitimacy : ChildDisciplineCreatesEthicalLegitimacy → ⊥
childDisciplineDoesNotCreateEthicalLegitimacy ()

experimentalEffectDoesNotSettleEthics : ExperimentalEffectSettlesEthics → ⊥
experimentalEffectDoesNotSettleEthics ()

socialPsychologyDoesNotEraseParticipantVoice : SocialPsychologyParentErasesParticipantVoice → ⊥
socialPsychologyDoesNotEraseParticipantVoice ()

record ChildhoodCategorisationConformityPsychologyBidiBoundary : Set where
  constructor childhood-categorisation-conformity-psychology-bidi-boundary
  field
    exactQidsAttachedWhenSafelyResolvable : Bool
    ambiguousCategorisationQidRemainsUnresolved : Bool
    conformityAndObedienceRemainDistinct : Bool
    outwardBehaviourDoesNotRecoverPrivateBelief : Bool
    assignedCategoryDoesNotBecomeIdentityTruth : Bool
    categoryGenesisRemainsAuditable : Bool
    childDisciplineDoesNotCreateLegitimateAuthority : Bool
    empiricalEffectDoesNotSettleEthics : Bool
    affectedParticipantVoiceRemainsIndependent : Bool
    nonfactorabilityMaySnowballNewAxes : Bool
    currentAxisVocabularyClaimedComplete : Bool
open ChildhoodCategorisationConformityPsychologyBidiBoundary public

canonicalChildhoodCategorisationConformityPsychologyBidiBoundary :
  ChildhoodCategorisationConformityPsychologyBidiBoundary
canonicalChildhoodCategorisationConformityPsychologyBidiBoundary =
  childhood-categorisation-conformity-psychology-bidi-boundary
    true true true true true true true true true true false

priorFormationBoundary : Prior.KinshipSocialisationEducationAuthorityBidiBoundary
priorFormationBoundary = Prior.canonicalKinshipSocialisationEducationAuthorityBidiBoundary
