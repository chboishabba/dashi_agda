module DASHI.Education.EKindyRelationalCommonsExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.PedagogicalJPlusOneRouting as JPlusOne
import DASHI.Biology.StudentIdentifiedSupportStrategiesBridge as Support
import DASHI.Education.EarlyLearningChoicePNFHyperfabricBridge as Existing

------------------------------------------------------------------------
-- EKINDY RELATIONAL COMMONS
--
-- This is a constructive architecture inspired by the Queensland eKindy model
-- discussed in the accompanying analysis: home/family delivery remains linked
-- to qualified professional support, a common curriculum/framework, situated
-- contextualisation and an evidence-return loop.
--
-- This module is not a claim that every eKindy implementation has every field
-- below, nor that the model should be universally substituted for centre-based
-- ECEC.  It formalises the relational topology relevant to the policy argument.
------------------------------------------------------------------------

record RelationalLearningLoop : Set where
  constructor relationalLearningLoop
  field
    qualifiedTeacherRelation : Bool
    qualifiedTeacherRelationIsTrue : qualifiedTeacherRelation ≡ true
    familyOrTutorRelation : Bool
    familyOrTutorRelationIsTrue : familyOrTutorRelation ≡ true
    commonLearningFramework : Bool
    commonLearningFrameworkIsTrue : commonLearningFramework ≡ true
    localContextCanReframeActivity : Bool
    localContextCanReframeActivityIsTrue : localContextCanReframeActivity ≡ true
    synchronousReviewAvailable : Bool
    synchronousReviewAvailableIsTrue : synchronousReviewAvailable ≡ true
    evidenceReturnAvailable : Bool
    evidenceReturnAvailableIsTrue : evidenceReturnAvailable ≡ true
    optionalNudgeLayer : Bool
    optionalNudgeLayerIsTrue : optionalNudgeLayer ≡ true
    nudgeIsPrimaryCareRelation : Bool
    nudgeIsPrimaryCareRelationIsFalse : nudgeIsPrimaryCareRelation ≡ false

open RelationalLearningLoop public

canonicalEKindyRelationalLoop : RelationalLearningLoop
canonicalEKindyRelationalLoop =
  relationalLearningLoop
    true refl true refl true refl true refl
    true refl true refl true refl false refl

------------------------------------------------------------------------
-- Contextualisation is not replacement of the curriculum carrier.  The same
-- common learning aim may be enacted through a situated family lifeworld.
------------------------------------------------------------------------

data LearningAim : Set where
  countingAim languageAim sequencingAim measurementAim narrativeAim : LearningAim

data LocalContext : Set where
  harvestingContext homeRoutineContext communityEventContext localCountryContext : LocalContext

record ContextualisedLearningActivity : Set where
  constructor contextualisedLearningActivity
  field
    commonAim : LearningAim
    localContext : LocalContext
    activityLabel : String
    commonAimRetained : Bool
    commonAimRetainedIsTrue : commonAimRetained ≡ true
    contextTreatedAsNoise : Bool
    contextTreatedAsNoiseIsFalse : contextTreatedAsNoise ≡ false

open ContextualisedLearningActivity public

harvestCountingActivity : ContextualisedLearningActivity
harvestCountingActivity =
  contextualisedLearningActivity
    countingAim harvestingContext
    "count, group or compare objects encountered during harvesting"
    true refl false refl

------------------------------------------------------------------------
-- Public pedagogical commons: resources are available across routes rather
-- than being conditional on withdrawal from professional ECEC.
------------------------------------------------------------------------

data CommonsResourceKind : Set where
  curriculumMap activityLibrary multilingualResource : CommonsResourceKind
  accessibilityResource localGroup professionalContact forumResource : CommonsResourceKind

canonicalCommonsResources : List CommonsResourceKind
canonicalCommonsResources =
  curriculumMap ∷ activityLibrary ∷ multilingualResource ∷ accessibilityResource
  ∷ localGroup ∷ professionalContact ∷ forumResource ∷ []

record PublicPedagogicalCommons : Set where
  constructor publicPedagogicalCommons
  field
    resources : List CommonsResourceKind
    availableToCentreUsers : Bool
    availableToCentreUsersIsTrue : availableToCentreUsers ≡ true
    availableToHomeUsers : Bool
    availableToHomeUsersIsTrue : availableToHomeUsers ≡ true
    availableToKinCarers : Bool
    availableToKinCarersIsTrue : availableToKinCarers ≡ true
    accessRequiresProfessionalExit : Bool
    accessRequiresProfessionalExitIsFalse : accessRequiresProfessionalExit ≡ false

open PublicPedagogicalCommons public

canonicalPublicPedagogicalCommons : PublicPedagogicalCommons
canonicalPublicPedagogicalCommons =
  publicPedagogicalCommons canonicalCommonsResources
    true refl true refl true refl false refl

------------------------------------------------------------------------
-- Nudge closure: the existing J+1 gate remains the governing boundary.  A
-- message may route attention, but cannot itself become care or pedagogical
-- authority.
------------------------------------------------------------------------

canonicalNudgeSafetyGate : JPlusOne.JPlusOneSafetyGate
canonicalNudgeSafetyGate = JPlusOne.canonicalJPlusOneSafetyGate

nudgeEqualsCareRemainsBlocked :
  JPlusOne.AdmissibleJPlusOnePromotionRoute JPlusOne.nudgeEqualsCareRoute →
  JPlusOne.Never
nudgeEqualsCareRemainsBlocked = JPlusOne.nudgeEqualsCareBlocked

------------------------------------------------------------------------
-- Support ecology: Alice/Getenet/Burke/Fanshawe support families are retained
-- as many-to-many candidate supports around the relational loop, not universal
-- prescriptions.
------------------------------------------------------------------------

canonicalStudentIdentifiedSupportBridge : Support.StudentIdentifiedSupportStrategiesBridge
canonicalStudentIdentifiedSupportBridge =
  Support.canonicalStudentIdentifiedSupportStrategiesBridge

------------------------------------------------------------------------
-- eKindy-like distribution is represented as a supported additional route,
-- not as a proof that the professional floor can be removed.
------------------------------------------------------------------------

ekindyLikeRouteRetainsExistingAdditionalityWitness :
  Existing.professionalFloorRetained Existing.supportedAdditionalAlternative ≡ true
ekindyLikeRouteRetainsExistingAdditionalityWitness = refl

relationalCommonsReading : String
relationalCommonsReading =
  "A distributed early-learning route can move activity into the home without turning home delivery into institutional exit: a qualified relation, common framework, local contextualisation, synchronous review, public commons and evidence return remain present, while optional nudges stay subordinate to the relational loop."
