module DASHI.Wikimedia.IbrahimSnowballKinshipSocialisationEducationAuthorityBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.SnowballPluralLensInvariantExact as Snowball
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballRitualMythCommunityInstitutionExact as Prior
import DASHI.Culture.ChildReligiousAutonomyFormationBidiExact as Formation
import DASHI.Culture.JohnAnthonyBrownStudyDesignBidiExact as BrownDesign
import DASHI.Governance.AliceBrownInstitutionalAgencyChoiceBridgeExact as Alice
import DASHI.Biology.EducationCorpusSourceRegistry as EducationSources

------------------------------------------------------------------------
-- IBRAHIM / SNOWBALL BIDI CONTINUATION:
--
--   ritual / community / institution
--           <-> kinship / family
--           <-> socialisation
--           <-> education
--           <-> authority
--
-- The traversal is bidirectional.  External concept-parent structure proposes
-- candidate seams; concrete DASHI counterexamples constrain the parent reading
-- in return.  Thus a parent cannot become a lossy explanation of its leaves.
--
-- External identity coordinates inspected 2026-09-10:
--   kinship                         Q171318
--   family                          Q8436
--   education                       Q8434
--   socialisation / socialization   Q185467
--   parent-child relationship       Q1334052
--   authority, hierarchical relation Q4825937
--   authority, legitimate decision power Q174834
--   Jane Elliott                    Q6152188
--   Alice Miller, psychologist      Q236384
--
-- The two authority QIDs are deliberately retained as different senses.  QIDs
-- identify external items; they do not establish consent, legitimacy, causal
-- mechanism, experimental validity, psychological truth, or cultural authority.
------------------------------------------------------------------------

kinshipQid : Identity.ExternalIdentityDemand
kinshipQid = Identity.mkOptionalIdentityDemand
  "Ibrahim kinship/socialisation/education BIDI"
  "external concept identity"
  "kinship"
  Identity.wikidataQid
  (Identity.verified "Q171318" "Wikidata concept identity checked 2026-09-10")

familyQid : Identity.ExternalIdentityDemand
familyQid = Identity.mkOptionalIdentityDemand
  "Ibrahim kinship/socialisation/education BIDI"
  "external concept identity"
  "family"
  Identity.wikidataQid
  (Identity.verified "Q8436" "Wikidata concept identity checked 2026-09-10")

educationQid : Identity.ExternalIdentityDemand
educationQid = Identity.mkOptionalIdentityDemand
  "Ibrahim kinship/socialisation/education BIDI"
  "external concept identity"
  "education"
  Identity.wikidataQid
  (Identity.verified "Q8434" "Wikidata concept identity checked 2026-09-10")

socialisationQid : Identity.ExternalIdentityDemand
socialisationQid = Identity.mkOptionalIdentityDemand
  "Ibrahim kinship/socialisation/education BIDI"
  "external concept identity"
  "socialisation / socialization"
  Identity.wikidataQid
  (Identity.verified "Q185467" "Wikidata social-learning concept identity checked 2026-09-10; not economic social ownership")

parentChildRelationshipQid : Identity.ExternalIdentityDemand
parentChildRelationshipQid = Identity.mkOptionalIdentityDemand
  "Ibrahim kinship/socialisation/education BIDI"
  "external concept identity"
  "parent-child relationship"
  Identity.wikidataQid
  (Identity.verified "Q1334052" "Wikidata relation identity checked 2026-09-10")

hierarchicalAuthorityQid : Identity.ExternalIdentityDemand
hierarchicalAuthorityQid = Identity.mkOptionalIdentityDemand
  "Ibrahim kinship/socialisation/education BIDI"
  "external concept identity / sense distinction"
  "authority as asymmetric or hierarchical social relation"
  Identity.wikidataQid
  (Identity.verified "Q4825937" "Wikidata authority sense checked 2026-09-10")

legitimateAuthorityQid : Identity.ExternalIdentityDemand
legitimateAuthorityQid = Identity.mkOptionalIdentityDemand
  "Ibrahim kinship/socialisation/education BIDI"
  "external concept identity / sense distinction"
  "authority as legitimate power to decide or authorise"
  Identity.wikidataQid
  (Identity.verified "Q174834" "Wikidata authority sense checked 2026-09-10")

janeElliottQid : Identity.ExternalIdentityDemand
janeElliottQid = Identity.mkOptionalIdentityDemand
  "Blue Eyes/Brown Eyes source-acquisition frontier"
  "person identity only; substantive exercise evidence remains source-bounded"
  "Jane Elliott"
  Identity.wikidataQid
  (Identity.verified "Q6152188" "Wikidata person identity checked 2026-09-10")

aliceMillerQid : Identity.ExternalIdentityDemand
aliceMillerQid = Identity.mkOptionalIdentityDemand
  "Alice Miller source-acquisition frontier"
  "person identity only; psychological claims require exact work/source receipts"
  "Alice Miller (Swiss psychologist, 1923-2010)"
  Identity.wikidataQid
  (Identity.verified "Q236384" "Wikidata person identity checked 2026-09-10; homonym disambiguated")

janeElliottCanonicalLink : Identity.ExternalIdentityDemand
janeElliottCanonicalLink = Identity.mkOptionalIdentityDemand
  "Blue Eyes/Brown Eyes source-acquisition frontier"
  "official/canonical external link"
  "Jane Elliott official website"
  Identity.canonicalURL
  (Identity.verified "https://janeelliott.com/" "official website coordinate exposed by current Wikidata item")

aliceMillerCanonicalLink : Identity.ExternalIdentityDemand
aliceMillerCanonicalLink = Identity.mkOptionalIdentityDemand
  "Alice Miller source-acquisition frontier"
  "official/canonical external link"
  "Alice Miller official website"
  Identity.canonicalURL
  (Identity.verified "http://www.alice-miller.com" "official website coordinate exposed by current Wikidata item")

------------------------------------------------------------------------
-- BIDI graph roles: candidate parent and concrete child each constrain the
-- other.  These are traversal coordinates, not a closed ontology.
------------------------------------------------------------------------

data FormationGraphNode : Set where
  kinshipNode familyNode socialisationNode educationNode authorityNode : FormationGraphNode

record BidiGraphAudit : Set where
  constructor bidi-graph-audit
  field
    node : FormationGraphNode
    upwardNavigationReading : String
    downwardRegressionReading : String
    principalWrongTypeRisk : String
    attributionRequired : Bool
    twoEyedComparisonRequired : Bool
    parentLabelExplainsEveryChildCase : Bool
open BidiGraphAudit public

kinshipAudit : BidiGraphAudit
kinshipAudit = bidi-graph-audit kinshipNode
  "relationship/network parent candidate joining family, descent, care, community and anthropology"
  "child-facing authority, voice, obligation and consent must still be separately recovered"
  "kin relation != unlimited decision authority != child assent != cultural authority"
  true true false

familyAudit : BidiGraphAudit
familyAudit = bidi-graph-audit familyNode
  "social-group/institution candidate adjacent to kinship, socialisation, care and education"
  "John Brown formation and Alice Brown observer fibres show that belonging/parent role cannot recover child agency"
  "family membership != parent testimony != child voice != legitimate authority"
  true true false

socialisationAudit : BidiGraphAudit
socialisationAudit = bidi-graph-audit socialisationNode
  "social-learning/transmission candidate linking community practice, family, education and institutions"
  "same outward participation can coexist with materially different refusal/revision/exit conditions"
  "socialisation != consent != private belief != autonomous endorsement"
  true true false

educationAudit : BidiGraphAudit
educationAudit = bidi-graph-audit educationNode
  "formal/informal learning parent candidate linking institutions, teachers, students, family and culture"
  "Alice Brown source-bound education corpus requires voice, accessibility, contestability and observer separation"
  "participation != agency; survey != voice; institutional record != whole educational system"
  true true false

authorityAudit : BidiGraphAudit
authorityAudit = bidi-graph-audit authorityNode
  "polysemous parent candidate spanning asymmetric social relation, legitimate authorisation, institutional office and community/cultural authority"
  "the two external authority senses plus Country/community/child-agency owners forbid silent sense substitution"
  "power asymmetry != legitimate authority != epistemic authority != community/Country authority"
  true true false

------------------------------------------------------------------------
-- Exact BIDI regression 1.
-- A socialisation/public-participation surface cannot recover autonomy.
------------------------------------------------------------------------

data SocialisationCase : Set where
  openSocialisationCase constrainedSocialisationCase : SocialisationCase

data SocialisationSurface : Set where sameOutwardParticipation : SocialisationSurface
data AutonomyReading : Set where revisableAutonomy constrainedAutonomy : AutonomyReading

socialisationSurface : SocialisationCase → SocialisationSurface
socialisationSurface _ = sameOutwardParticipation

autonomyReading : SocialisationCase → AutonomyReading
autonomyReading openSocialisationCase = revisableAutonomy
autonomyReading constrainedSocialisationCase = constrainedAutonomy

socialisationAutonomyDefect :
  INF.NonFactorabilityWitness socialisationSurface autonomyReading
socialisationAutonomyDefect = INF.nonFactorabilityWitness
  openSocialisationCase constrainedSocialisationCase refl (λ ())

socialisationCannotFactorAutonomy :
  INF.FactorsThrough socialisationSurface autonomyReading → ⊥
socialisationCannotFactorAutonomy =
  INF.witnessRulesOutEveryFlatFactorisation socialisationAutonomyDefect

formationSameSurfaceReceipt :
  Formation.publicSurface Formation.openFormationEpisode ≡
  Formation.publicSurface Formation.closedFormationEpisode
formationSameSurfaceReceipt = Formation.samePublicParticipationDifferentAutonomy

participationStillDoesNotCreateConsent : Formation.ParticipationPromotesConsent → ⊥
participationStillDoesNotCreateConsent = Formation.participationDoesNotPromoteConsent

------------------------------------------------------------------------
-- Exact BIDI regression 2.
-- A family/kinship relation cannot recover child-facing agency conditions.
------------------------------------------------------------------------

data KinshipAgencyCase : Set where
  sameFamilyChildCanContest sameFamilyChildCannotContest : KinshipAgencyCase

data FamilySurface : Set where sameFamilyRelation : FamilySurface
data ChildAgencyReading : Set where contestableAgency noncontestableAgency : ChildAgencyReading

familySurface : KinshipAgencyCase → FamilySurface
familySurface _ = sameFamilyRelation

childAgencyReading : KinshipAgencyCase → ChildAgencyReading
childAgencyReading sameFamilyChildCanContest = contestableAgency
childAgencyReading sameFamilyChildCannotContest = noncontestableAgency

familyAgencyDefect : INF.NonFactorabilityWitness familySurface childAgencyReading
familyAgencyDefect = INF.nonFactorabilityWitness
  sameFamilyChildCanContest sameFamilyChildCannotContest refl (λ ())

familyRelationCannotFactorChildAgency :
  INF.FactorsThrough familySurface childAgencyReading → ⊥
familyRelationCannotFactorChildAgency =
  INF.witnessRulesOutEveryFlatFactorisation familyAgencyDefect

------------------------------------------------------------------------
-- Exact BIDI regression 3.
-- "Authority" cannot silently quotient hierarchical power and legitimate
-- authorisation into one recoverable sense.
------------------------------------------------------------------------

data AuthoritySituatedCase : Set where
  sameAuthorityWordHierarchyOnly sameAuthorityWordLegitimated : AuthoritySituatedCase

data AuthorityWordSurface : Set where authorityWord : AuthorityWordSurface
data AuthoritySense : Set where hierarchicalRelationSense legitimateDecisionSense : AuthoritySense

authorityWordSurface : AuthoritySituatedCase → AuthorityWordSurface
authorityWordSurface _ = authorityWord

authoritySense : AuthoritySituatedCase → AuthoritySense
authoritySense sameAuthorityWordHierarchyOnly = hierarchicalRelationSense
authoritySense sameAuthorityWordLegitimated = legitimateDecisionSense

authoritySenseDefect : INF.NonFactorabilityWitness authorityWordSurface authoritySense
authoritySenseDefect = INF.nonFactorabilityWitness
  sameAuthorityWordHierarchyOnly sameAuthorityWordLegitimated refl (λ ())

authorityWordCannotFactorAuthoritySense :
  INF.FactorsThrough authorityWordSurface authoritySense → ⊥
authorityWordCannotFactorAuthoritySense =
  INF.witnessRulesOutEveryFlatFactorisation authoritySenseDefect

------------------------------------------------------------------------
-- Existing Alice Brown education/agency owners constrain the parent graph.
------------------------------------------------------------------------

aliceAgencyBoundary : Alice.AliceInstitutionalChoiceBoundary
aliceAgencyBoundary = Alice.canonicalAliceInstitutionalChoiceBoundary

formalOptionStillDoesNotCreateAgency : Alice.FormalOptionPromotesAgency → ⊥
formalOptionStillDoesNotCreateAgency = Alice.formalOptionDoesNotPromoteAgency

parentReportStillDoesNotCreateChildVoice : Alice.ParentReportPromotesChildVoiceIdentity → ⊥
parentReportStillDoesNotCreateChildVoice = Alice.parentReportDoesNotPromoteChildVoiceIdentity

institutionRecordStillDoesNotCreateWholeSystem : Alice.InstitutionRecordPromotesWholeSystemView → ⊥
institutionRecordStillDoesNotCreateWholeSystem = Alice.institutionRecordDoesNotPromoteWholeSystemView

aliceVoicePaper : EducationSources.PaperReference
aliceVoicePaper = EducationSources.voiceAgencyPaper

aliceParentAllyshipPaper : EducationSources.PaperReference
aliceParentAllyshipPaper = EducationSources.parentalAllyshipLensPaper

------------------------------------------------------------------------
-- Snowball as proof-search / experimental-design discipline.
-- A graph edge yields a consumer obligation, not a conclusion.  Evidence is
-- admissible relative to that exact obligation. Nonfactorability, WrongType,
-- source-role failure, negative cases, divergence or silence reopen the lens.
------------------------------------------------------------------------

record BidiEvidenceDesignPayment : Set where
  constructor bidi-evidence-design-payment
  field
    graphRelationCreatesSearchObligation : Bool
    evidenceAdmissibilityIsObligationRelative : Bool
    samplingFrameRetainedWhenRelevant : Bool
    comparatorRetainedWhenRelevant : Bool
    measurementValidityRetainedWhenRelevant : Bool
    confoundingRetainedWhenRelevant : Bool
    uncertaintyRetainedWhenRelevant : Bool
    participantRoleRetainedWhenRelevant : Bool
    qualitativeDivergenceMaySurvive : Bool
    qualitativeSilenceMaySurvive : Bool
    nonfactorabilityTriggersLensReopening : Bool
    wrongTypeTriggersRoleDisambiguation : Bool
    attributionTravelsWithEvidence : Bool
    oneExperimentSettlesParentNode : Bool
open BidiEvidenceDesignPayment public

canonicalBidiEvidenceDesignPayment : BidiEvidenceDesignPayment
canonicalBidiEvidenceDesignPayment = bidi-evidence-design-payment
  true true true true true true true true true true true true true false

brownDesignBoundary : BrownDesign.JohnAnthonyBrownStudyDesignBoundary
brownDesignBoundary = BrownDesign.canonicalJohnAnthonyBrownStudyDesignBoundary

brownMixedMethods : BrownDesign.MixedMethodsIntegrationReceipt
brownMixedMethods = BrownDesign.canonicalMixedMethodsIntegration

------------------------------------------------------------------------
-- Jane Elliott and Alice Miller enter at the source-acquisition boundary.
-- Their stable person identities are retained now, but source propositions are
-- not invented.  Blue Eyes/Brown Eyes is a useful candidate experimental /
-- performative categorisation probe; Alice Miller is a useful candidate
-- historical/psychological childhood-authority source lane.  Exact claims must
-- be attached to exact works/records before they pay any empirical obligation.
------------------------------------------------------------------------

record NamedSourceFrontier : Set where
  constructor named-source-frontier
  field
    personQidResolved : Bool
    canonicalLinkRequested : Bool
    exactWorkSourceStillRequired : Bool
    personIdentityCreatesEmpiricalValidity : Bool
    personIdentityCreatesDomainAuthority : Bool
open NamedSourceFrontier public

janeElliottFrontier : NamedSourceFrontier
janeElliottFrontier = named-source-frontier true true true false false

aliceMillerFrontier : NamedSourceFrontier
aliceMillerFrontier = named-source-frontier true true true false false

------------------------------------------------------------------------
-- The local plural-lens specimen is explicitly contingent. It demonstrates
-- that the BIDI graph can discover new axes without making them global names.
------------------------------------------------------------------------

data LocalFormationAxis : Set where
  relationAxis voiceAgencyAxis refusalRevisionAxis observerAxis authoritySenseAxis
  sourceRoleAxis designAxis historicalTransmissionAxis : LocalFormationAxis

localRelevant : LocalFormationAxis → Bool
localRelevant _ = true

localRetained : LocalFormationAxis → Bool
localRetained _ = true

localFormationLens : Snowball.PluralLens LocalFormationAxis
localFormationLens = Snowball.plural-lens localRelevant localRetained (λ _ _ → refl)

attributionBoundary : AttributionSnowball.AttributionSnowballBoundary
attributionBoundary = AttributionSnowball.canonicalAttributionSnowballBoundary

priorRitualBoundary : Prior.RitualMythCommunityInstitutionBoundary
priorRitualBoundary = Prior.canonicalRitualMythCommunityInstitutionBoundary

record KinshipSocialisationEducationAuthorityBidiBoundary : Set where
  constructor kinship-socialisation-education-authority-bidi-boundary
  field
    externalIdentityRequestedWhenAvailable : Bool
    graphTraversalIsBidirectional : Bool
    concreteChildrenConstrainParentSemantics : Bool
    parentLabelsMayNotEraseChildResiduals : Bool
    socialisationDoesNotCreateConsent : Bool
    educationDoesNotCreateAutonomousEndorsement : Bool
    kinshipDoesNotCreateUnlimitedChildDecisionAuthority : Bool
    hierarchicalPowerDoesNotCreateLegitimateAuthority : Bool
    participantVoiceNotReplacedByInstitutionalRecord : Bool
    evidenceDesignIsObligationRelative : Bool
    nonfactorabilityReopensPluralLens : Bool
    attributionSnowballsWithEvidence : Bool
    twoEyedSituatedCommunityFibreRetained : Bool
    currentAxisVocabularyClaimedComplete : Bool
open KinshipSocialisationEducationAuthorityBidiBoundary public

canonicalKinshipSocialisationEducationAuthorityBidiBoundary :
  KinshipSocialisationEducationAuthorityBidiBoundary
canonicalKinshipSocialisationEducationAuthorityBidiBoundary =
  kinship-socialisation-education-authority-bidi-boundary
    true true true true true true true true true true true true true false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SocialisationCreatesConsent : Set where
data EducationCreatesAutonomousEndorsement : Set where
data KinshipCreatesUnlimitedChildDecisionAuthority : Set where
data HierarchicalPowerCreatesLegitimateAuthority : Set where
data AuthorityQidSenseCanBeSilentlySwapped : Set where
data FamilyReportCreatesChildVoice : Set where
data ExperimentalParticipationCreatesEndorsement : Set where
data JaneElliottQidCreatesExperimentalValidity : Set where
data AliceMillerQidCreatesPsychologicalTruth : Set where
data InstitutionalEducationCreatesCommunityCountryAuthority : Set where
data BidiParentLabelExplainsEveryChildCase : Set where
data QidCreatesAuthorityOrProof : Set where

socialisationDoesNotCreateConsent : SocialisationCreatesConsent → ⊥
socialisationDoesNotCreateConsent ()

educationDoesNotCreateAutonomousEndorsement : EducationCreatesAutonomousEndorsement → ⊥
educationDoesNotCreateAutonomousEndorsement ()

kinshipDoesNotCreateUnlimitedDecisionAuthority : KinshipCreatesUnlimitedChildDecisionAuthority → ⊥
kinshipDoesNotCreateUnlimitedDecisionAuthority ()

hierarchicalPowerDoesNotCreateLegitimateAuthority : HierarchicalPowerCreatesLegitimateAuthority → ⊥
hierarchicalPowerDoesNotCreateLegitimateAuthority ()

authorityQidSensesCannotBeSilentlySwapped : AuthorityQidSenseCanBeSilentlySwapped → ⊥
authorityQidSensesCannotBeSilentlySwapped ()

familyReportDoesNotCreateChildVoice : FamilyReportCreatesChildVoice → ⊥
familyReportDoesNotCreateChildVoice ()

experimentalParticipationDoesNotCreateEndorsement : ExperimentalParticipationCreatesEndorsement → ⊥
experimentalParticipationDoesNotCreateEndorsement ()

janeElliottQidDoesNotCreateExperimentalValidity : JaneElliottQidCreatesExperimentalValidity → ⊥
janeElliottQidDoesNotCreateExperimentalValidity ()

aliceMillerQidDoesNotCreatePsychologicalTruth : AliceMillerQidCreatesPsychologicalTruth → ⊥
aliceMillerQidDoesNotCreatePsychologicalTruth ()

institutionalEducationDoesNotCreateCountryAuthority : InstitutionalEducationCreatesCommunityCountryAuthority → ⊥
institutionalEducationDoesNotCreateCountryAuthority ()

bidiParentLabelDoesNotExplainEveryChild : BidiParentLabelExplainsEveryChildCase → ⊥
bidiParentLabelDoesNotExplainEveryChild ()

qidDoesNotCreateAuthorityOrProof : QidCreatesAuthorityOrProof → ⊥
qidDoesNotCreateAuthorityOrProof ()
