module DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRound16Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.IntersectionalNonFactorability as Intersection
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity

------------------------------------------------------------------------
-- ROUND 16: DESIGN EXCLUSION / AFFECTED-BUT-UNSAMPLED OBSERVERS.
--
-- Python/Pareto recutting after Round 15 moved the deepest frontier from
-- eligible-but-missing to two distinct residuals:
--   * who is structurally excluded by a delivery/design choice; and
--   * who bears the consequences of a data/platform practice without being
--     represented in the realised study participant carrier.
--
-- External sources own only bounded observations. DASHI owns the finite
-- non-factorability witnesses below. Affected population != sampled population;
-- adult proxy/institutional observation != child participant authority.
------------------------------------------------------------------------

data Round16Residual : Set where
  blanketOnlineDesignByClassMaterialExclusion : Round16Residual
  childDataSubjectByAdultObserverCarrier : Round16Residual
  parentLabourByStudentDatafication : Round16Residual
  platformisationByPluralSchoolObserver : Round16Residual

record Round16Candidate : Set where
  constructor round16-candidate
  field
    source : Attr.AttributedSource
    sourceRoleReceipt : Snowball.SourceRoleSnowballReceipt source
    qidDemand : Identity.ExternalIdentityDemand
    deweyState : String
    targetResidual : Round16Residual
    sourceBoundedReading : String
    limitation : String
    includedInFinalCorpus : Bool
    includedInFinalCorpusIsFalse : includedInFinalCorpus ≡ false

open Round16Candidate public

mkRound16Candidate :
  (source : Attr.AttributedSource) →
  Round16Residual → String → String →
  Round16Candidate
mkRound16Candidate source residual reading limitation =
  round16-candidate
    source
    (Snowball.canonicalSourceRoleSnowballReceipt source)
    (Identity.mkOptionalIdentityDemand
      "DigitalESDIntersectionalSourceAcquisitionParetoRound16Exact"
      (Attr.sourceTitle source)
      (Attr.sourceTitle source)
      Identity.wikidataQid
      (Identity.unresolved "no independently verified same-object publication QID recorded by round 16"))
    "Dewey coordinate unresolved; no nearest-label substitution"
    residual reading limitation false refl

------------------------------------------------------------------------
-- Hlatshwayo 2022: blanket online transition x poor/working-class exclusion.
------------------------------------------------------------------------

hlatshwayoOnlineLockdownSource : Attr.AttributedSource
hlatshwayoOnlineLockdownSource = Attr.mkDOISource
  "Mondli Shadrack Hlatshwayo"
  "Online Learning during the South African Covid-19 Lockdown: University Students Left to Their Own Devices"
  "Education as Change 26"
  "2022"
  "10.25159/1947-9417/11155"
  "https://doi.org/10.25159/1947-9417/11155"
  Attr.academicArticleSource
  "South African higher-education qualitative study based on in-depth interviews with students and lecturers plus internet sources. It reports that the lockdown shift to online learning exposed substantial participation deficiencies for students from poor and working-class households where reliable ICT access could not be assumed."
  Attr.publicAttribution

hlatshwayoCandidate : Round16Candidate
hlatshwayoCandidate = mkRound16Candidate
  hlatshwayoOnlineLockdownSource
  blanketOnlineDesignByClassMaterialExclusion
  "Direct design-exclusion donor: the institutional move to one online delivery surface does not imply equal practical participation when device, connectivity and household material conditions differ."
  "Pandemic-era South African qualitative evidence; it does not establish that all online education excludes poor/working-class students, that online delivery alone caused every difficulty, or a universal population effect."

------------------------------------------------------------------------
-- Spina et al. 2026: children are data subjects; adult institutional actors are
-- the realised study participants.
------------------------------------------------------------------------

spinaFirstYearDataficationSource : Attr.AttributedSource
spinaFirstYearDataficationSource = Attr.mkDOISource
  "Nerida Spina; Rebecca Spooner-Lane; Emily Seager; Jeanine Gallagher; Susan Danby"
  "Datafication in the First Year of Schooling"
  "Australasian Journal of Early Childhood 51(1), 48-60"
  "2026 issue / 2025 online"
  "10.1177/18369391251358010"
  "https://doi.org/10.1177/18369391251358010"
  Attr.academicArticleSource
  "Queensland early-years study in two outer-regional primary schools. Six Prep teachers and four school-authority staff were the study participants while the practices under discussion involved digital and administrative data collected about children in their first year of formal schooling."
  Attr.publicAttribution

spinaCandidate : Round16Candidate
spinaCandidate = mkRound16Candidate
  spinaFirstYearDataficationSource
  childDataSubjectByAdultObserverCarrier
  "Strong affected-but-unsampled discriminator: children are the subjects of the data systems and intended beneficiaries/objects of support, yet the realised participant carrier is composed of teachers and school-authority staff. This makes affected child position distinct from adult institutional interpretation."
  "The paper explicitly studies teacher/authority perspectives and does not claim to report children's first-person experiences. Child absence from the participant carrier must not be converted into a claim that teachers cannot know or support children, nor into child participant authority."

------------------------------------------------------------------------
-- Cayas et al. 2026: student data reorganise parent/family labour; inquiry starts
-- from parents and selected school staff, not the children whose achievement data
-- organise the relations being traced.
------------------------------------------------------------------------

cayasParentDataficationSource : Attr.AttributedSource
cayasParentDataficationSource = Attr.mkDOISource
  "Annetta Cayas; Nerida Spina; Karen Dooley; Janet Rankin"
  "Parent engagement in the achievement society: the intensification of parenting for the datafied student subject"
  "British Journal of Sociology of Education, advance online publication"
  "2026"
  "10.1080/01425692.2026.2632302"
  "https://doi.org/10.1080/01425692.2026.2632302"
  Attr.academicArticleSource
  "Australian institutional ethnography beginning with interviews with ten parents and then school staff. It traces how school-produced student achievement data and parent-engagement expectations organise parent labour, family relations and ways of knowing children as datafied student subjects."
  Attr.publicAttribution

cayasCandidate : Round16Candidate
cayasCandidate = mkRound16Candidate
  cayasParentDataficationSource
  parentLabourByStudentDatafication
  "High-alpha social-provisioning/externality donor: educational data practices can relocate work and performance pressure into family life. The children whose achievement data organise those relations are affected parties while parents/staff supply the empirical participant viewpoints in this study."
  "One comparatively advantaged Australian school and primarily parent/staff observer evidence. Parent labour findings do not establish children's own interpretation, all-family incidence, causal effects of one platform, or one political conclusion."

------------------------------------------------------------------------
-- Gouseti/Shaw 2026: plural school observers expose distributed platform burden.
------------------------------------------------------------------------

gousetiShawPlatformisationSource : Attr.AttributedSource
gousetiShawPlatformisationSource = Attr.mkDOISource
  "Anastasia Gouseti; Patricia Shaw"
  "When platformisation meets schooling: exploring teachers, students and parents' experiences of digital platform use"
  "Learning, Media and Technology, advance online publication"
  "2026"
  "10.1080/17439884.2026.2653746"
  "https://doi.org/10.1080/17439884.2026.2653746"
  Attr.academicArticleSource
  "Qualitative study across two secondary schools in England drawing on school leaders, teachers, students and parents. It reports valued administrative/communication efficiencies alongside monitoring/surveillance, professionalisation of parenting, digital exclusion and teacher digital-wellbeing concerns."
  Attr.publicAttribution

gousetiShawCandidate : Round16Candidate
gousetiShawCandidate = mkRound16Candidate
  gousetiShawPlatformisationSource
  platformisationByPluralSchoolObserver
  "Plural-observer comparator: platformisation changes different positions in different ways, so a school-level efficiency surface cannot stand in for parent, teacher or student incidence. This helps distinguish observer coverage from decision authority."
  "Two-school qualitative study. Including several observer groups does not create exhaustive representation, equal decision authority, universal platform harms, or a material-lifecycle measurement."

canonicalRound16Frontier : List Round16Candidate
canonicalRound16Frontier =
  spinaCandidate
  ∷ hlatshwayoCandidate
  ∷ cayasCandidate
  ∷ gousetiShawCandidate
  ∷ []

------------------------------------------------------------------------
-- DASHI-owned collision 1: same formal online-delivery surface can coexist with
-- different material participation adequacy.
------------------------------------------------------------------------

data DesignExclusionWorld : Set where
  sameOnlineSurfaceMateriallySupported : DesignExclusionWorld
  sameOnlineSurfaceMateriallyExcluded : DesignExclusionWorld

data OnlineDeliverySurface : Set where
  sameOnlineDelivery : OnlineDeliverySurface

deliverySurfaceProjection : DesignExclusionWorld → OnlineDeliverySurface
deliverySurfaceProjection sameOnlineSurfaceMateriallySupported = sameOnlineDelivery
deliverySurfaceProjection sameOnlineSurfaceMateriallyExcluded = sameOnlineDelivery

participationAdequacy : DesignExclusionWorld → Bool
participationAdequacy sameOnlineSurfaceMateriallySupported = true
participationAdequacy sameOnlineSurfaceMateriallyExcluded = false

participationAdequacyDiffers :
  participationAdequacy sameOnlineSurfaceMateriallySupported ≡
  participationAdequacy sameOnlineSurfaceMateriallyExcluded → ⊥
participationAdequacyDiffers ()

designExclusionWitness :
  Intersection.NonFactorabilityWitness deliverySurfaceProjection participationAdequacy
designExclusionWitness =
  Intersection.nonFactorabilityWitness
    sameOnlineSurfaceMateriallySupported
    sameOnlineSurfaceMateriallyExcluded
    refl participationAdequacyDiffers

DesignExclusionFactorisation : Set₁
DesignExclusionFactorisation =
  Intersection.FactorsThrough deliverySurfaceProjection participationAdequacy

designExclusionDoesNotFactorThroughDeliverySurface :
  DesignExclusionFactorisation → ⊥
designExclusionDoesNotFactorThroughDeliverySurface =
  Intersection.witnessRulesOutEveryFlatFactorisation designExclusionWitness

------------------------------------------------------------------------
-- DASHI-owned collision 2: same institutional data-practice surface can coexist
-- with child/affected-party observer inclusion or exclusion.
------------------------------------------------------------------------

data AffectedObserverWorld : Set where
  sameInstitutionalSurfaceAffectedVoicePresent : AffectedObserverWorld
  sameInstitutionalSurfaceAffectedVoiceAbsent : AffectedObserverWorld

data InstitutionalDataSurface : Set where
  sameInstitutionalDataPractice : InstitutionalDataSurface

institutionalSurfaceProjection : AffectedObserverWorld → InstitutionalDataSurface
institutionalSurfaceProjection sameInstitutionalSurfaceAffectedVoicePresent = sameInstitutionalDataPractice
institutionalSurfaceProjection sameInstitutionalSurfaceAffectedVoiceAbsent = sameInstitutionalDataPractice

affectedObserverAdequacy : AffectedObserverWorld → Bool
affectedObserverAdequacy sameInstitutionalSurfaceAffectedVoicePresent = true
affectedObserverAdequacy sameInstitutionalSurfaceAffectedVoiceAbsent = false

affectedObserverAdequacyDiffers :
  affectedObserverAdequacy sameInstitutionalSurfaceAffectedVoicePresent ≡
  affectedObserverAdequacy sameInstitutionalSurfaceAffectedVoiceAbsent → ⊥
affectedObserverAdequacyDiffers ()

affectedObserverWitness :
  Intersection.NonFactorabilityWitness institutionalSurfaceProjection affectedObserverAdequacy
affectedObserverWitness =
  Intersection.nonFactorabilityWitness
    sameInstitutionalSurfaceAffectedVoicePresent
    sameInstitutionalSurfaceAffectedVoiceAbsent
    refl affectedObserverAdequacyDiffers

AffectedObserverFactorisation : Set₁
AffectedObserverFactorisation =
  Intersection.FactorsThrough institutionalSurfaceProjection affectedObserverAdequacy

affectedObserverDoesNotFactorThroughInstitutionalSurface :
  AffectedObserverFactorisation → ⊥
affectedObserverDoesNotFactorThroughInstitutionalSurface =
  Intersection.witnessRulesOutEveryFlatFactorisation affectedObserverWitness

------------------------------------------------------------------------
-- No-promotion / observer-role firewalls.
------------------------------------------------------------------------

data Round16CandidateCreatesIncludedStudy : Set where
data AffectedPopulationCreatesSampledPopulationIdentity : Set where
data AdultInstitutionalObserverCreatesChildParticipantAuthority : Set where
data OnlineDeliveryCreatesParticipationAdequacy : Set where
data PluralObserverCoverageCreatesDecisionAuthority : Set where

round16CandidateDoesNotCreateIncludedStudy :
  Round16CandidateCreatesIncludedStudy → ⊥
round16CandidateDoesNotCreateIncludedStudy ()

affectedPopulationDoesNotCreateSampledPopulationIdentity :
  AffectedPopulationCreatesSampledPopulationIdentity → ⊥
affectedPopulationDoesNotCreateSampledPopulationIdentity ()

adultInstitutionalObserverDoesNotCreateChildParticipantAuthority :
  AdultInstitutionalObserverCreatesChildParticipantAuthority → ⊥
adultInstitutionalObserverDoesNotCreateChildParticipantAuthority ()

onlineDeliveryDoesNotCreateParticipationAdequacy :
  OnlineDeliveryCreatesParticipationAdequacy → ⊥
onlineDeliveryDoesNotCreateParticipationAdequacy ()

pluralObserverCoverageDoesNotCreateDecisionAuthority :
  PluralObserverCoverageCreatesDecisionAuthority → ⊥
pluralObserverCoverageDoesNotCreateDecisionAuthority ()

round16Reading : String
round16Reading =
  "Round 16 follows the Python residual frontier after hidden-population Round 15. Hlatshwayo pays a source-bounded poor/working-class participation constraint under a common online-delivery transition; Spina et al. make children visible as data subjects while teachers/authority staff constitute the study participant carrier; Cayas et al. trace parent/family labour organised by student data; Gouseti/Shaw provide a plural school-observer platformisation comparator. DASHI separately owns two finite non-factorability witnesses: formal online delivery cannot recover participation adequacy, and an institutional data-practice surface cannot recover whether affected-party observer coverage is adequate. None of these candidate sources is thereby admitted to the final review corpus."
