module DASHI.Education.EarlyLearningIntersectionalCapabilityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as Intersection
import DASHI.Education.EarlyLearningChoicePNFHyperfabricBridge as Existing

------------------------------------------------------------------------
-- INTERSECTIONAL EARLY-LEARNING CAPABILITY
--
-- The policy subject is not a scalar "family".  Child, caregiver, household,
-- place, labour, disability/access, culture/language, gendered care burden,
-- community authority and institutional relation remain independently visible.
--
-- This module proves carrier/non-factorability statements only.  It does not
-- assign empirical outcomes to real demographic groups.
------------------------------------------------------------------------

data ChildPosition : Set where
  childPositionA childPositionB : ChildPosition

data CaregiverPosition : Set where
  caregiverPositionA caregiverPositionB : CaregiverPosition

data HouseholdPosition : Set where
  householdPositionA householdPositionB : HouseholdPosition

data PlacePosition : Set where
  urban regional remote : PlacePosition

data LabourPosition : Set where
  secureFlexible precariousTimePoor : LabourPosition

data AccessPosition : Set where
  ordinaryAccess specialistAccessRequired : AccessPosition

data CultureLanguagePosition : Set where
  dominantLanguage multilingualOrCommunityLanguage : CultureLanguagePosition

data GenderedCarePosition : Set where
  lowerCareBurden higherCareBurden : GenderedCarePosition

data CommunityAuthorityPosition : Set where
  nuclearHouseholdOnly kinCommunityGoverned : CommunityAuthorityPosition

data InstitutionalRelation : Set where
  institutionTrusted institutionMixed institutionHistoricallyUnsafe : InstitutionalRelation

record SituatedEarlyLearningPosition : Set where
  constructor situatedEarlyLearningPosition
  field
    child : ChildPosition
    caregiver : CaregiverPosition
    household : HouseholdPosition
    place : PlacePosition
    labour : LabourPosition
    access : AccessPosition
    cultureLanguage : CultureLanguagePosition
    genderedCare : GenderedCarePosition
    communityAuthority : CommunityAuthorityPosition
    institutionalRelation : InstitutionalRelation

open SituatedEarlyLearningPosition public

data PublicFamilyChoiceLabel : Set where
  sameFormalFamilyChoice : PublicFamilyChoiceLabel

familyChoiceProjection : SituatedEarlyLearningPosition → PublicFamilyChoiceLabel
familyChoiceProjection position = sameFormalFamilyChoice

------------------------------------------------------------------------
-- Finite witness: same family-choice label, different effective capability.
-- Bool is a structural witness only, not an empirical score.
------------------------------------------------------------------------

lowReachabilityPosition : SituatedEarlyLearningPosition
lowReachabilityPosition =
  situatedEarlyLearningPosition
    childPositionA caregiverPositionA householdPositionA
    urban precariousTimePoor specialistAccessRequired
    multilingualOrCommunityLanguage higherCareBurden
    nuclearHouseholdOnly institutionMixed

highReachabilityPosition : SituatedEarlyLearningPosition
highReachabilityPosition =
  situatedEarlyLearningPosition
    childPositionB caregiverPositionB householdPositionB
    urban secureFlexible ordinaryAccess
    dominantLanguage lowerCareBurden
    kinCommunityGoverned institutionTrusted

effectiveCapabilityWitness : SituatedEarlyLearningPosition → Bool
effectiveCapabilityWitness lowReachabilityPosition = false
effectiveCapabilityWitness highReachabilityPosition = true
effectiveCapabilityWitness position = false

sameChoiceDifferentCapability :
  effectiveCapabilityWitness lowReachabilityPosition ≡
  effectiveCapabilityWitness highReachabilityPosition → ⊥
sameChoiceDifferentCapability ()

familyChoiceIntersectionalNonFactorability :
  Intersection.NonFactorabilityWitness
    familyChoiceProjection effectiveCapabilityWitness
familyChoiceIntersectionalNonFactorability =
  Intersection.nonFactorabilityWitness
    lowReachabilityPosition highReachabilityPosition refl
    sameChoiceDifferentCapability

familyChoiceCannotDetermineEffectiveCapability :
  Intersection.FactorsThrough
    familyChoiceProjection effectiveCapabilityWitness → ⊥
familyChoiceCannotDetermineEffectiveCapability =
  Intersection.witnessRulesOutEveryFlatFactorisation
    familyChoiceIntersectionalNonFactorability

------------------------------------------------------------------------
-- Family agency is not parental sovereignty.
-- Authority remains fibred across child, family, kin/community and profession.
------------------------------------------------------------------------

data AuthorityDomain : Set where
  childPreferenceDomain familyContextDomain kinCommunityDomain : AuthorityDomain
  professionalPedagogyDomain safeguardingDomain publicEntitlementDomain : AuthorityDomain

data AuthorityHolder : Set where
  childHolder familyHolder kinCommunityHolder professionalHolder publicHolder : AuthorityHolder

canonicalAuthorityHolder : AuthorityDomain → AuthorityHolder
canonicalAuthorityHolder childPreferenceDomain = childHolder
canonicalAuthorityHolder familyContextDomain = familyHolder
canonicalAuthorityHolder kinCommunityDomain = kinCommunityHolder
canonicalAuthorityHolder professionalPedagogyDomain = professionalHolder
canonicalAuthorityHolder safeguardingDomain = publicHolder
canonicalAuthorityHolder publicEntitlementDomain = publicHolder

parentalSovereigntyOverEveryDomain : Bool
parentalSovereigntyOverEveryDomain = false

parentalSovereigntyOverEveryDomainIsFalse :
  parentalSovereigntyOverEveryDomain ≡ false
parentalSovereigntyOverEveryDomainIsFalse = refl

------------------------------------------------------------------------
-- Equity is topological/capability-sensitive: different deficits may require
-- different support kinds, not merely a larger scalar transfer.
------------------------------------------------------------------------

data SupportKind : Set where
  connectivitySupport teacherContactSupport incomeTimeSupport transportSupport : SupportKind
  multilingualSupport culturalGovernanceSupport specialistSupport accessibilitySupport : SupportKind
  peerCommunitySupport respiteSupport professionalECECSupport : SupportKind

supportKindsForPlace : PlacePosition → List SupportKind
supportKindsForPlace remote = connectivitySupport ∷ teacherContactSupport ∷ []
supportKindsForPlace regional = transportSupport ∷ teacherContactSupport ∷ []
supportKindsForPlace urban = professionalECECSupport ∷ []

supportKindsForAccess : AccessPosition → List SupportKind
supportKindsForAccess ordinaryAccess = []
supportKindsForAccess specialistAccessRequired = specialistSupport ∷ accessibilitySupport ∷ []

supportKindsForCulture : CultureLanguagePosition → List SupportKind
supportKindsForCulture dominantLanguage = []
supportKindsForCulture multilingualOrCommunityLanguage = multilingualSupport ∷ culturalGovernanceSupport ∷ []

sameChequeIsNotDefinedAsEquity : Bool
sameChequeIsNotDefinedAsEquity = false

sameChequeIsNotDefinedAsEquityIsFalse : sameChequeIsNotDefinedAsEquity ≡ false
sameChequeIsNotDefinedAsEquityIsFalse = refl

------------------------------------------------------------------------
-- Reuse the prior addition/substitution theorem as one fibre of the enlarged
-- situated capability carrier.
------------------------------------------------------------------------

expandedChoiceStillDoesNotDetermineProfessionalFloor :
  Intersection.NonFactorabilityWitness
    Existing.expandedChoiceProjection Existing.professionalFloorRetained
expandedChoiceStillDoesNotDetermineProfessionalFloor =
  Existing.expandedChoiceDoesNotDetermineProfessionalFloor

intersectionalCapabilityReading : String
intersectionalCapabilityReading =
  "Family choice is one observation surface over a multi-actor situated capability system. Child, family, kin/community, professional and public authority remain coordinate-specific; equal transfers need not create equal reachable opportunity, and equity may require different kinds of connection rather than only more of the same scalar resource."
