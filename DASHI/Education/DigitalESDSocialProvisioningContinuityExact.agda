module DASHI.Education.DigitalESDSocialProvisioningContinuityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.IntersectionalNonFactorability as Intersection
import DASHI.Education.CommunityConnectednessTopologyExact as Community
import DASHI.Education.DigitalESDDisabilityIntersectionalityAuditExact as Disability
import DASHI.Education.DigitalESDStudyIntersectionalAbsenceAuditExact as Absence

------------------------------------------------------------------------
-- SOCIAL PROVISIONING CONTINUITY
--
-- Instruction is only one service supplied through schooling.  A delivery-mode
-- change must not silently erase meals, safe space, community connection, care,
-- accessibility support, device/connectivity access or household burdens.
------------------------------------------------------------------------

duellQueenslandBreakfastSource : Attr.AttributedSource
duellQueenslandBreakfastSource = Attr.mkDOISource
  "Rebecca Duell; Danielle Villoresi; Nomxolisi Malope-Rwodzi; Danielle Gallegos"
  "Beyond Breakfast: Exploring What Works for Schools Delivering School Breakfast Programs in Queensland, Australia"
  "Health Promotion Journal of Australia"
  "2026"
  "10.1002/hpja.70193"
  "https://doi.org/10.1002/hpja.70193"
  Attr.academicArticleSource
  "Primary/evaluation evidence concerning school-based food-relief delivery in Queensland. Supports bounded claims about hunger relief and implementation features of the evaluated programmes; it does not prove that online schooling causes food insecurity or that every school meal programme has identical effects."
  Attr.publicAttribution

heersCommunitySchoolsReview : Attr.AttributedSource
heersCommunitySchoolsReview = Attr.mkDOISource
  "Marieke Heers; Chris Van Klaveren; Wim Groot; Henriëtte Maassen van den Brink"
  "Community Schools: What We Know and What We Need to Know"
  "Review of Educational Research 86(4)"
  "2016"
  "10.3102/0034654315627365"
  "https://doi.org/10.3102/0034654315627365"
  Attr.academicArticleSource
  "Review source characterising community schools as integrated educational/social-service arrangements involving institutional cooperation, parents and extracurricular activity, while explicitly noting limits in the effectiveness evidence. Does not establish universal superiority of community schools."
  Attr.publicAttribution

canonicalSocialProvisioningSourceAtlas : Attr.AttributedSourceAtlas
canonicalSocialProvisioningSourceAtlas = Attr.mkSourceAtlas
  "digital ESD social provisioning continuity source atlas"
  "DASHI.Education.DigitalESDSocialProvisioningContinuityExact"
  (duellQueenslandBreakfastSource ∷ heersCommunitySchoolsReview ∷ [])
  "School food relief and community-school evidence are retained as source-bounded provisioning evidence; neither source is promoted into a universal delivery-mode causal claim."

data SocialProvisioningCoordinate : Set where
  mealsFoodSecurity : SocialProvisioningCoordinate
  safeGatheringDwellSpace : SocialProvisioningCoordinate
  peerAdultConnection : SocialProvisioningCoordinate
  healthSocialServiceLinkage : SocialProvisioningCoordinate
  familyCommunityConnection : SocialProvisioningCoordinate
  informalObservationSupport : SocialProvisioningCoordinate
  disabilityAccessSupport : SocialProvisioningCoordinate
  deviceConnectivityAccess : SocialProvisioningCoordinate
  householdCareSupervisionBurden : SocialProvisioningCoordinate
  transportTravelBurden : SocialProvisioningCoordinate
  extracurricularCommunityParticipation : SocialProvisioningCoordinate

socialProvisioningCoordinates : List SocialProvisioningCoordinate
socialProvisioningCoordinates =
  mealsFoodSecurity
  ∷ safeGatheringDwellSpace
  ∷ peerAdultConnection
  ∷ healthSocialServiceLinkage
  ∷ familyCommunityConnection
  ∷ informalObservationSupport
  ∷ disabilityAccessSupport
  ∷ deviceConnectivityAccess
  ∷ householdCareSupervisionBurden
  ∷ transportTravelBurden
  ∷ extracurricularCommunityParticipation
  ∷ []

------------------------------------------------------------------------
-- Same instructional surface, different social-provisioning bundle.
------------------------------------------------------------------------

data DeliveryWorld : Set where
  sameInstructionProvisionRetained : DeliveryWorld
  sameInstructionProvisionShifted : DeliveryWorld

data InstructionSurface : Set where sameInstruction : InstructionSurface

instructionProjection : DeliveryWorld → InstructionSurface
instructionProjection sameInstructionProvisionRetained = sameInstruction
instructionProjection sameInstructionProvisionShifted = sameInstruction

socialProvisioningAdequate : DeliveryWorld → Bool
socialProvisioningAdequate sameInstructionProvisionRetained = true
socialProvisioningAdequate sameInstructionProvisionShifted = false

sameInstruction :
  instructionProjection sameInstructionProvisionRetained ≡
  instructionProjection sameInstructionProvisionShifted
sameInstruction = refl

provisioningDiffers :
  socialProvisioningAdequate sameInstructionProvisionRetained ≡
  socialProvisioningAdequate sameInstructionProvisionShifted → ⊥
provisioningDiffers ()

instructionalDeliveryProvisioningWitness :
  Intersection.NonFactorabilityWitness instructionProjection socialProvisioningAdequate
instructionalDeliveryProvisioningWitness =
  Intersection.nonFactorabilityWitness
    sameInstructionProvisionRetained
    sameInstructionProvisionShifted
    refl
    provisioningDiffers

instructionalDeliveryCannotDetermineSocialProvisioning :
  Intersection.FactorsThrough instructionProjection socialProvisioningAdequate → ⊥
instructionalDeliveryCannotDetermineSocialProvisioning =
  Intersection.witnessRulesOutEveryFlatFactorisation instructionalDeliveryProvisioningWitness

communityBoundary : Community.CommunityConnectednessBoundary
communityBoundary = Community.canonicalCommunityConnectednessBoundary

record SocialProvisioningIntersectionalChallenge : Set where
  constructor social-provisioning-intersectional-challenge
  field
    disabilityBoundary : Disability.DisabilityDigitalESDBoundary
    absenceAuditQuestionCount : Agda.Builtin.Nat.Nat
    communityBoundary : Community.CommunityConnectednessBoundary
    challengeReading : String

open SocialProvisioningIntersectionalChallenge public

canonicalSocialProvisioningIntersectionalChallenge : SocialProvisioningIntersectionalChallenge
canonicalSocialProvisioningIntersectionalChallenge = social-provisioning-intersectional-challenge
  Disability.canonicalDisabilityDigitalESDBoundary
  Absence.absenceAuditQuestionCount
  Community.canonicalCommunityConnectednessBoundary
  "When instructional delivery changes, audit who loses or gains meals, safe space, connection, disability/access support, device/connectivity, care/supervision, transport relief or other services; affected-but-unsampled households and communities remain visible."

record SocialProvisioningBoundary : Set where
  constructor social-provisioning-boundary
  field
    instructionEqualsCompleteProvisioning : Bool
    instructionEqualsCompleteProvisioningIsFalse : instructionEqualsCompleteProvisioning ≡ false
    formalCommunityLinkEqualsEffectiveConnection : Bool
    formalCommunityLinkEqualsEffectiveConnectionIsFalse : formalCommunityLinkEqualsEffectiveConnection ≡ false
    schoolMealEvidenceCreatesOnlineHungerCausation : Bool
    schoolMealEvidenceCreatesOnlineHungerCausationIsFalse : schoolMealEvidenceCreatesOnlineHungerCausation ≡ false
    intersectionalChallengeRequired : Bool
    intersectionalChallengeRequiredIsTrue : intersectionalChallengeRequired ≡ true

open SocialProvisioningBoundary public

canonicalSocialProvisioningBoundary : SocialProvisioningBoundary
canonicalSocialProvisioningBoundary = social-provisioning-boundary
  false refl
  false refl
  false refl
  true refl
