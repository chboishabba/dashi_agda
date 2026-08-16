module DASHI.Governance.EffectiveInstitutionalChoiceExact where

------------------------------------------------------------------------
-- EFFECTIVE INSTITUTIONAL CHOICE
--
-- Formal availability of multiple institutions does not imply that a person
-- can actually use more than one.  Accessibility is coordinatewise here:
-- distance/transport, money, waiting time, specialist capability,
-- disability access, language/cultural access, and legal eligibility remain
-- distinct bottlenecks.
--
-- Cross-pollination sources / vocabulary:
--
-- Alice Brown; Megan Kimber,
-- "Repositioning Student Voice and Agency: A Call for the Epistemic Expansion
-- of Scholarship of Teaching and Learning Inquiry",
-- Active Learning in Higher Education 27(2):253--264 (2026),
-- DOI 10.1177/14697874261426374.
-- Source role: participation/agency correction; formal solicitation or
-- invitation does not by itself constitute agency.
--
-- Seyum Getenet; Katie Burke; Melissa Fanshawe; Alice Brown,
-- "Supporting online learning in teacher education: student-identified
-- strategies and social constructivist implications", Distance Education
-- (2026, online first), DOI 10.1080/01587919.2026.2669288.
-- Source role: context-bound evidence that accessibility, autonomy/flexibility,
-- interaction and scaffolding are distinct support dimensions; not a universal
-- institutional-choice theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.StudentVoiceEpistemicAgencyBridge as Voice
import DASHI.Biology.EducationCorpusSourceRegistry as EducationSources
import DASHI.Governance.MultidimensionalContestabilityAccessExact as Access

record InstitutionalAccessProfile : Set where
  constructor institutionalAccessProfile
  field
    distanceTransport : Nat
    money : Nat
    waitingTime : Nat
    specialistCapability : Nat
    disabilityAccess : Nat
    languageCulturalAccess : Nat
    legalEligibility : Nat

open InstitutionalAccessProfile public

record SubjectCapacity : Set where
  constructor subjectCapacity
  field
    distanceTransportCapacity : Nat
    moneyCapacity : Nat
    waitingTimeCapacity : Nat
    specialistRequirement : Nat
    disabilityRequirement : Nat
    languageCulturalRequirement : Nat
    legalEligibilityCapacity : Nat

open SubjectCapacity public

record EffectivelyAccessible
    (demand : InstitutionalAccessProfile)
    (capacity : SubjectCapacity) : Set where
  constructor effectivelyAccessible
  field
    distanceWitness : distanceTransport demand ≤ distanceTransportCapacity capacity
    moneyWitness : money demand ≤ moneyCapacity capacity
    waitingWitness : waitingTime demand ≤ waitingTimeCapacity capacity
    specialistWitness : specialistCapability demand ≤ specialistRequirement capacity
    disabilityWitness : disabilityAccess demand ≤ disabilityRequirement capacity
    languageWitness : languageCulturalAccess demand ≤ languageCulturalRequirement capacity
    eligibilityWitness : legalEligibility demand ≤ legalEligibilityCapacity capacity

open EffectivelyAccessible public

data Provider : Set where
  religiousSchool secularSchool : Provider

formalProviders : List Provider
formalProviders = religiousSchool ∷ secularSchool ∷ []

religiousSchoolDemand : InstitutionalAccessProfile
religiousSchoolDemand = institutionalAccessProfile 1 1 1 1 1 1 1

secularSchoolDemand : InstitutionalAccessProfile
secularSchoolDemand = institutionalAccessProfile 5 1 1 1 1 1 1

canonicalFamilyCapacity : SubjectCapacity
canonicalFamilyCapacity = subjectCapacity 2 2 2 2 2 2 2

religiousSchoolAccessible :
  EffectivelyAccessible religiousSchoolDemand canonicalFamilyCapacity
religiousSchoolAccessible =
  effectivelyAccessible (s≤s z≤n) (s≤s z≤n) (s≤s z≤n)
    (s≤s z≤n) (s≤s z≤n) (s≤s z≤n) (s≤s z≤n)

secularSchoolNotAccessible :
  EffectivelyAccessible secularSchoolDemand canonicalFamilyCapacity → ⊥
secularSchoolNotAccessible access =
  impossible (distanceWitness access)
  where
    impossible : 5 ≤ 2 → ⊥
    impossible ()

------------------------------------------------------------------------
-- Formal plurality and effective plurality are separate propositions.
------------------------------------------------------------------------

data FormalPluralityPromotesEffectivePlurality : Set where

formalPluralityDoesNotPromoteEffectivePlurality :
  FormalPluralityPromotesEffectivePlurality → ⊥
formalPluralityDoesNotPromoteEffectivePlurality ()

data OnlyAccessibleProviderIsReligiousPromotesCoercion : Set where

religiousAvailabilityDoesNotEstablishCoercion :
  OnlyAccessibleProviderIsReligiousPromotesCoercion → ⊥
religiousAvailabilityDoesNotEstablishCoercion ()

------------------------------------------------------------------------
-- Reuse the Alice Brown student-agency correction: invitation/presence is not
-- partnership/agency.  This is a methodological analogy across domains, not
-- an assertion that the education paper empirically establishes healthcare or
-- religious-service access.
------------------------------------------------------------------------

aliceInvitationNotPartnershipBoundary :
  Voice.AdmissibleVoicePromotionRoute Voice.invitationEqualsPartnershipRoute →
  Voice.Never
aliceInvitationNotPartnershipBoundary = Voice.invitationEqualsPartnershipBlocked

aliceVoiceSource : EducationSources.PaperReference
aliceVoiceSource = EducationSources.voiceAgencyPaper

aliceSupportSource : EducationSources.PaperReference
aliceSupportSource = EducationSources.onlineSupportStrategiesPaper

record EffectiveInstitutionalChoiceBoundary : Set where
  constructor effectiveInstitutionalChoiceBoundary
  field
    formalPluralityEqualsEffectivePlurality : Bool
    coordinateBottleneckCanDestroyEffectiveAlternative : Bool
    onlyAccessibleReligiousProviderEqualsCoercion : Bool
    formalInvitationEqualsAgency : Bool
    accessibilityIsMultidimensional : Bool

canonicalEffectiveInstitutionalChoiceBoundary : EffectiveInstitutionalChoiceBoundary
canonicalEffectiveInstitutionalChoiceBoundary =
  effectiveInstitutionalChoiceBoundary false true false false true
