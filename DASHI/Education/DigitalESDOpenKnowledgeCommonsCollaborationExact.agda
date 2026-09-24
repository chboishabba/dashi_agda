module DASHI.Education.DigitalESDOpenKnowledgeCommonsCollaborationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Education.DigitalESDAcquisitionSnowballParetoExact as Acquisition
import DASHI.Biology.StudentVoiceEpistemicAgencyBridge as Voice

------------------------------------------------------------------------
-- OPEN KNOWLEDGE COMMONS / COLLABORATIVE CURRICULUM BRIDGE
--
-- This owner treats openness, collaboration, multilinguality, accessibility,
-- provenance and educational authority as distinct coordinates.  It does not
-- infer educational effectiveness from open-source practice, nor open-source
-- licensing from public GitHub visibility.
------------------------------------------------------------------------

unescoOERRecommendationSource : Attr.AttributedSource
unescoOERRecommendationSource =
  Attr.mkNoDOISource
    "UNESCO General Conference"
    "Recommendation on Open Educational Resources (OER)"
    "UNESCO, 40th General Conference"
    "2019"
    "https://www.unesco.org/en/legal-affairs/recommendation-open-educational-resources-oer"
    Attr.institutionalSource
    "Primary normative OER source. Supports open licensing, no-cost access, reuse, repurposing, adaptation, redistribution, translation, accessible formats, multilingual/local-language resources, co-creation and international collaboration. It does not establish that a particular public repository is legally open licensed, accessible, inclusive or educationally effective."
    Attr.publicAttribution

unicefAccessibleDigitalTextbooksSource : Attr.AttributedSource
unicefAccessibleDigitalTextbooksSource =
  Attr.mkNoDOISource
    "UNICEF"
    "Accessible Digital Textbooks for All"
    "UNICEF Digital Education"
    "2026"
    "https://www.unicef.org/digitaleducation/reports/accessible-digital-textbooks-all"
    Attr.institutionalSource
    "Primary UNICEF accessibility source for flexible digital learning materials, disability inclusion and systems-oriented accessible textbook design. Accessibility features and disability participation remain separate from open licensing and from proof of learning effectiveness."
    Attr.publicAttribution

castUDLThreeSource : Attr.AttributedSource
castUDLThreeSource =
  Attr.mkNoDOISource
    "CAST"
    "Universal Design for Learning Guidelines version 3.0"
    "CAST"
    "2024"
    "https://udlguidelines.cast.org/"
    Attr.institutionalSource
    "Primary UDL guidance emphasizing learner agency, multiple means of representation/action/expression, accessible technologies, multilingual and multimodal representation, collective learning and reduction of exclusionary barriers. It is a design framework, not an intervention-effect estimate."
    Attr.publicAttribution

publicPlatformCharterSource : Attr.AttributedSource
publicPlatformCharterSource = Acquisition.publicDigitalLearningPlatformCharterSource

commonsSources : List Attr.AttributedSource
commonsSources =
  unescoOERRecommendationSource
  ∷ publicPlatformCharterSource
  ∷ unicefAccessibleDigitalTextbooksSource
  ∷ castUDLThreeSource
  ∷ []

commonsSourceCount : Nat
commonsSourceCount = 4

------------------------------------------------------------------------
-- Shared stakeholder carrier.
------------------------------------------------------------------------

data StakeholderRole : Set where
  learnerStakeholder : StakeholderRole
  teacherStakeholder : StakeholderRole
  parentFamilyStakeholder : StakeholderRole
  curriculumStewardStakeholder : StakeholderRole
  communityContributorStakeholder : StakeholderRole

stakeholderRoles : List StakeholderRole
stakeholderRoles =
  learnerStakeholder
  ∷ teacherStakeholder
  ∷ parentFamilyStakeholder
  ∷ curriculumStewardStakeholder
  ∷ communityContributorStakeholder
  ∷ []

stakeholderRoleCount : Nat
stakeholderRoleCount = 5

-- A stakeholder role is a collaboration coordinate, not automatic authority.
data StakeholderRoleCreatesUniversalAuthority : Set where
stakeholderRoleDoesNotCreateUniversalAuthority : StakeholderRoleCreatesUniversalAuthority → ⊥
stakeholderRoleDoesNotCreateUniversalAuthority ()

------------------------------------------------------------------------
-- Commons affordances.  These can coexist in different combinations.
------------------------------------------------------------------------

data CommonsAffordance : Set where
  publicRead : CommonsAffordance
  legallyReusable : CommonsAffordance
  forkAndAdapt : CommonsAffordance
  proposeRevision : CommonsAffordance
  discussAndReview : CommonsAffordance
  multilingualAdaptation : CommonsAffordance
  multimodalRepresentation : CommonsAffordance
  assistiveTechnologyCompatibility : CommonsAffordance
  offlineLowConnectivityAccess : CommonsAffordance
  provenanceRetainingHistory : CommonsAffordance
  externalEntityLinking : CommonsAffordance

canonicalCommonsAffordances : List CommonsAffordance
canonicalCommonsAffordances =
  publicRead
  ∷ legallyReusable
  ∷ forkAndAdapt
  ∷ proposeRevision
  ∷ discussAndReview
  ∷ multilingualAdaptation
  ∷ multimodalRepresentation
  ∷ assistiveTechnologyCompatibility
  ∷ offlineLowConnectivityAccess
  ∷ provenanceRetainingHistory
  ∷ externalEntityLinking
  ∷ []

------------------------------------------------------------------------
-- Public contribution interface is not enough to recover inclusive
-- participation.  The two worlds below expose the same open contribution
-- surface while differing in disability/language/connectivity participation.
------------------------------------------------------------------------

data CommonsState : Set where
  openButExclusionary : CommonsState
  openAndSituatedInclusive : CommonsState

data ContributionInterface : Set where
  publicContributionInterface : ContributionInterface

data InclusiveParticipation : Set where
  participationBlocked : InclusiveParticipation
  participationEnabled : InclusiveParticipation

contributionInterface : CommonsState → ContributionInterface
contributionInterface openButExclusionary = publicContributionInterface
contributionInterface openAndSituatedInclusive = publicContributionInterface

inclusiveParticipation : CommonsState → InclusiveParticipation
inclusiveParticipation openButExclusionary = participationBlocked
inclusiveParticipation openAndSituatedInclusive = participationEnabled

inclusiveParticipationDiffers :
  inclusiveParticipation openButExclusionary ≡
  inclusiveParticipation openAndSituatedInclusive → ⊥
inclusiveParticipationDiffers ()

openContributionWitness :
  INF.NonFactorabilityWitness contributionInterface inclusiveParticipation
openContributionWitness =
  INF.nonFactorabilityWitness
    openButExclusionary
    openAndSituatedInclusive
    refl
    inclusiveParticipationDiffers

OpenContributionInterfaceDeterminesInclusiveParticipation : Set₁
OpenContributionInterfaceDeterminesInclusiveParticipation =
  INF.FactorsThrough contributionInterface inclusiveParticipation

openContributionInterfaceDoesNotDetermineInclusiveParticipation :
  OpenContributionInterfaceDeterminesInclusiveParticipation → ⊥
openContributionInterfaceDoesNotDetermineInclusiveParticipation =
  INF.witnessRulesOutEveryFlatFactorisation openContributionWitness

------------------------------------------------------------------------
-- DASHI as an implementation fixture, not educational-effect evidence.
------------------------------------------------------------------------

record PublicRepositoryFixture : Set where
  constructor public-repository-fixture
  field
    repositoryReference : String
    publicVisibilityObserved : Bool
    publicVisibilityObservedIsTrue : publicVisibilityObserved ≡ true
    issuesEnabledObserved : Bool
    issuesEnabledObservedIsTrue : issuesEnabledObserved ≡ true
    wikiEnabledObserved : Bool
    wikiEnabledObservedIsTrue : wikiEnabledObserved ≡ true
    forksObserved : Bool
    forksObservedIsTrue : forksObserved ≡ true
    explicitRepositoryLicenseReceiptObserved : Bool
    explicitRepositoryLicenseReceiptObservedIsFalse :
      explicitRepositoryLicenseReceiptObserved ≡ false
    fixtureBoundary : String

open PublicRepositoryFixture public

dashiPublicRepositoryFixture : PublicRepositoryFixture
dashiPublicRepositoryFixture =
  public-repository-fixture
    "https://github.com/chboishabba/dashi_agda; GitHub repository metadata observed 2026-09-17"
    true refl
    true refl
    true refl
    true refl
    false refl
    "GitHub reports dashi_agda visibility=public, has_issues=true, has_wiki=true, forks=2, and license=null. This pays a public/versioned collaboration fixture only. It does not pay an OSI/open-source or OER reuse licence, accessibility, curriculum quality, inclusive participation or educational effectiveness."

userSuppliedCollaborationIntent : String
userSuppliedCollaborationIntent =
  "Design intent supplied in conversation: use the public DASHI knowledge base as a shared learning/curriculum substrate that students, teachers, parents/families, curriculum stewards and wider communities can inspect, discuss, adapt, translate and contribute to, with wiki/forum-style collaboration, multimodal representations and externally linked concept identities. This is a design fixture, not an observed educational outcome."

studentVoiceBoundaryRetained : Voice.StudentVoiceEpistemicAgencyBridge
studentVoiceBoundaryRetained = Voice.canonicalStudentVoiceEpistemicAgencyBridge

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data PublicVisibilityCreatesOpenLicense : Set where
data OpenLicenseCreatesAccessibility : Set where
data QIDLinkCreatesClaimTruth : Set where
data MultimodalCreatesAccessibility : Set where
data GlobalAvailabilityCreatesInclusiveParticipation : Set where
data OpenSourceCreatesEnvironmentalSustainability : Set where
data ContributionOpportunityCreatesUptake : Set where
data TranslationCreatesSemanticEquivalence : Set where
data OpenCommonsCreatesLearningEffect : Set where

publicVisibilityDoesNotCreateOpenLicense : PublicVisibilityCreatesOpenLicense → ⊥
publicVisibilityDoesNotCreateOpenLicense ()
openLicenseDoesNotCreateAccessibility : OpenLicenseCreatesAccessibility → ⊥
openLicenseDoesNotCreateAccessibility ()
qidLinkDoesNotCreateClaimTruth : QIDLinkCreatesClaimTruth → ⊥
qidLinkDoesNotCreateClaimTruth ()
multimodalDoesNotCreateAccessibility : MultimodalCreatesAccessibility → ⊥
multimodalDoesNotCreateAccessibility ()
globalAvailabilityDoesNotCreateInclusiveParticipation : GlobalAvailabilityCreatesInclusiveParticipation → ⊥
globalAvailabilityDoesNotCreateInclusiveParticipation ()
openSourceDoesNotCreateEnvironmentalSustainability : OpenSourceCreatesEnvironmentalSustainability → ⊥
openSourceDoesNotCreateEnvironmentalSustainability ()
contributionOpportunityDoesNotCreateUptake : ContributionOpportunityCreatesUptake → ⊥
contributionOpportunityDoesNotCreateUptake ()
translationDoesNotCreateSemanticEquivalence : TranslationCreatesSemanticEquivalence → ⊥
translationDoesNotCreateSemanticEquivalence ()
openCommonsDoesNotCreateLearningEffect : OpenCommonsCreatesLearningEffect → ⊥
openCommonsDoesNotCreateLearningEffect ()

record OpenKnowledgeCommonsBoundary : Set where
  constructor open-knowledge-commons-boundary
  field
    publicRepositoryFixtureObserved : Bool
    publicRepositoryFixtureObservedIsTrue : publicRepositoryFixtureObserved ≡ true
    publicVisibilityCreatesOpenLicense : Bool
    publicVisibilityCreatesOpenLicenseIsFalse : publicVisibilityCreatesOpenLicense ≡ false
    openLicenseCreatesAccessibility : Bool
    openLicenseCreatesAccessibilityIsFalse : openLicenseCreatesAccessibility ≡ false
    qidLinkCreatesClaimTruth : Bool
    qidLinkCreatesClaimTruthIsFalse : qidLinkCreatesClaimTruth ≡ false
    multimodalCreatesAccessibility : Bool
    multimodalCreatesAccessibilityIsFalse : multimodalCreatesAccessibility ≡ false
    globalAvailabilityCreatesInclusiveParticipation : Bool
    globalAvailabilityCreatesInclusiveParticipationIsFalse : globalAvailabilityCreatesInclusiveParticipation ≡ false
    openSourceCreatesEnvironmentalSustainability : Bool
    openSourceCreatesEnvironmentalSustainabilityIsFalse : openSourceCreatesEnvironmentalSustainability ≡ false
    contributionOpportunityCreatesUptake : Bool
    contributionOpportunityCreatesUptakeIsFalse : contributionOpportunityCreatesUptake ≡ false
    translationCreatesSemanticEquivalence : Bool
    translationCreatesSemanticEquivalenceIsFalse : translationCreatesSemanticEquivalence ≡ false
    openCommonsCreatesLearningEffect : Bool
    openCommonsCreatesLearningEffectIsFalse : openCommonsCreatesLearningEffect ≡ false
    multilingualAccessibleCommonsIsIndependentDesignRequirement : Bool
    multilingualAccessibleCommonsIsIndependentDesignRequirementIsTrue :
      multilingualAccessibleCommonsIsIndependentDesignRequirement ≡ true
    stakeholderCollaborationRetainsRoleAndProvenance : Bool
    stakeholderCollaborationRetainsRoleAndProvenanceIsTrue :
      stakeholderCollaborationRetainsRoleAndProvenance ≡ true

open OpenKnowledgeCommonsBoundary public

canonicalOpenKnowledgeCommonsBoundary : OpenKnowledgeCommonsBoundary
canonicalOpenKnowledgeCommonsBoundary =
  open-knowledge-commons-boundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl

openKnowledgeCommonsReading : String
openKnowledgeCommonsReading =
  "The stronger digital-ESD architecture is a shared knowledge commons rather than a one-way content-delivery platform: learner, teacher, parent/family, curriculum-steward and community roles can inspect, discuss, revise, adapt, translate and contribute while provenance and role remain explicit. UNESCO OER and the 2026 public-platform Charter support open licensing, reuse, interoperability, multilinguality and collaboration; UNICEF/CAST support disability accessibility, multimodal representation and learner agency. None of public visibility, open licensing, QID linking, multimodality or global reach alone establishes inclusive participation, semantic truth, educational effectiveness or environmental sustainability."
