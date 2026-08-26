module DASHI.Biology.SocialEcologicalAffordanceConeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.IntersectionalLongitudinalResidualDynamics as Intersectional
import DASHI.Biology.NeurodivergentSocialEcologySourceRegistryExact as Sources
import DASHI.Governance.BritishColumbiaDecriminalizationBundleExact as BC

------------------------------------------------------------------------
-- SOCIAL-ECOLOGICAL AFFORDANCE CONE
--
-- Accessibility and participation are modeled relationally.  The realized
-- action cone depends on person-state, built environment, social norm regime,
-- institution/governance, and relation context.  This is a finite DASHI
-- translation of social-ecological/affordance ideas, not a theorem asserted by
-- any one cited source.
------------------------------------------------------------------------

data PersonKind : Set where
  genericPerson autisticPerson neurodivergentPerson unhousedPerson : PersonKind

data BuiltEnvironment : Set where
  adjustableRetreatSpace denseUncontrolledSpace segmentedHostileSpace neutralPublicSpace : BuiltEnvironment

data SocialNormRegime : Set where
  lowDemandNorms conformityDemandNorms exclusionaryNorms : SocialNormRegime

data InstitutionalRegime : Set where
  permissiveRegime partialPermissionRegime restrictiveRegime : InstitutionalRegime

data RelationContext : Set where
  aloneRelation trustedFriendRelation unknownRelation : RelationContext

data Action : Set where
  enterAction remainAction restAction recoverAction observeAction interactAction declineInteractionAction leaveAction returnAction sleepAction : Action

record Ecology : Set where
  constructor ecology
  field
    built : BuiltEnvironment
    norms : SocialNormRegime
    institution : InstitutionalRegime
    relation : RelationContext

open Ecology public

record SituatedPerson : Set where
  constructor situatedPerson
  field
    personKind : PersonKind
    axisBundle : List Intersectional.IntersectionalAxis

open SituatedPerson public

------------------------------------------------------------------------
-- Finite realized-affordance relation.
------------------------------------------------------------------------

available : SituatedPerson → Ecology → Action → Bool
available person (ecology segmentedHostileSpace norms institution relation) sleepAction = false
available person (ecology denseUncontrolledSpace conformityDemandNorms restrictiveRegime relation) remainAction = false
available person (ecology denseUncontrolledSpace conformityDemandNorms restrictiveRegime relation) recoverAction = false
available person (ecology denseUncontrolledSpace conformityDemandNorms restrictiveRegime relation) declineInteractionAction = false
available person (ecology denseUncontrolledSpace conformityDemandNorms partialPermissionRegime aloneRelation) recoverAction = false
available person (ecology denseUncontrolledSpace conformityDemandNorms partialPermissionRegime aloneRelation) remainAction = false
available person (ecology adjustableRetreatSpace lowDemandNorms permissiveRegime relation) action = true
available person (ecology adjustableRetreatSpace lowDemandNorms partialPermissionRegime relation) action = true
available person (ecology neutralPublicSpace lowDemandNorms permissiveRegime relation) action = true
available person (ecology neutralPublicSpace norms restrictiveRegime sleepRelation) action = true
  where
  sleepRelation = unknownRelation
available person ecology action = true

canonicalAutisticPerson : SituatedPerson
canonicalAutisticPerson =
  situatedPerson autisticPerson Intersectional.canonicalIntersectionalAxes

canonicalUnhousedPerson : SituatedPerson
canonicalUnhousedPerson =
  situatedPerson unhousedPerson Intersectional.canonicalIntersectionalAxes

hostileEcology : Ecology
hostileEcology =
  ecology segmentedHostileSpace exclusionaryNorms restrictiveRegime unknownRelation

thirdPlaceEcology : Ecology
thirdPlaceEcology =
  ecology adjustableRetreatSpace lowDemandNorms permissiveRegime trustedFriendRelation

highDemandEcology : Ecology
highDemandEcology =
  ecology denseUncontrolledSpace conformityDemandNorms restrictiveRegime aloneRelation

------------------------------------------------------------------------
-- Same person, different ecology, different realized cone.
------------------------------------------------------------------------

samePersonChangedEcologyCanOpenRemain :
  available canonicalAutisticPerson highDemandEcology remainAction
  ≡ available canonicalAutisticPerson thirdPlaceEcology remainAction → ⊥
samePersonChangedEcologyCanOpenRemain ()

samePersonChangedEcologyCanOpenRecovery :
  available canonicalAutisticPerson highDemandEcology recoverAction
  ≡ available canonicalAutisticPerson thirdPlaceEcology recoverAction → ⊥
samePersonChangedEcologyCanOpenRecovery ()

environmentalRepairCanEnlargeConeWithoutChangingPerson :
  available canonicalAutisticPerson thirdPlaceEcology remainAction ≡ true
environmentalRepairCanEnlargeConeWithoutChangingPerson = refl

------------------------------------------------------------------------
-- Third-place bundle: presence does not force interaction.
------------------------------------------------------------------------

thirdPlaceSupportsPresence :
  available canonicalAutisticPerson thirdPlaceEcology remainAction ≡ true
thirdPlaceSupportsPresence = refl

thirdPlaceSupportsOptionalInteraction :
  available canonicalAutisticPerson thirdPlaceEcology interactAction ≡ true
thirdPlaceSupportsOptionalInteraction = refl

thirdPlaceSupportsDecliningInteraction :
  available canonicalAutisticPerson thirdPlaceEcology declineInteractionAction ≡ true
thirdPlaceSupportsDecliningInteraction = refl

thirdPlaceSupportsExitAndReturn :
  available canonicalAutisticPerson thirdPlaceEcology leaveAction ≡ true
  × available canonicalAutisticPerson thirdPlaceEcology returnAction ≡ true
thirdPlaceSupportsExitAndReturn = refl , refl

------------------------------------------------------------------------
-- Hostile architecture: exclusionary effect and exclusionary intent are kept
-- distinct.  The finite hostile specimen contracts sleep/rest affordances; it
-- does not infer intent from effect for an arbitrary environment.
------------------------------------------------------------------------

data DesignIntent : Set where
  exclusionaryIntent inclusiveIntent unknownIntent : DesignIntent

record DesignedEcology : Set where
  constructor designedEcology
  field
    ecologyState : Ecology
    designIntent : DesignIntent

open DesignedEcology public

canonicalHostileDesign : DesignedEcology
canonicalHostileDesign = designedEcology hostileEcology exclusionaryIntent

hostileDesignContractsSleep :
  available canonicalUnhousedPerson hostileEcology sleepAction ≡ false
hostileDesignContractsSleep = refl

data RestrictiveEffectImpliesIntentPermission : Set where

restrictiveEffectDoesNotAutoProveIntent :
  RestrictiveEffectImpliesIntentPermission → ⊥
restrictiveEffectDoesNotAutoProveIntent ()

------------------------------------------------------------------------
-- Political/institutional ordering can change realized affordances even when
-- the built geometry is held fixed.
------------------------------------------------------------------------

sameBuiltSpacePermissive : Ecology
sameBuiltSpacePermissive =
  ecology neutralPublicSpace lowDemandNorms permissiveRegime unknownRelation

sameBuiltSpaceRestrictive : Ecology
sameBuiltSpaceRestrictive =
  ecology neutralPublicSpace exclusionaryNorms restrictiveRegime unknownRelation

institutionCanChangeConeWithoutRebuildingSpace :
  institution sameBuiltSpacePermissive ≡ institution sameBuiltSpaceRestrictive → ⊥
institutionCanChangeConeWithoutRebuildingSpace ()

record PoliticalBoundary : Set where
  constructor politicalBoundary
  field
    conservativeIdentityImpliesHostileDesignApproval : Bool
    conservativeIdentityImpliesHostileDesignApprovalIsFalse :
      conservativeIdentityImpliesHostileDesignApproval ≡ false
    ideologicalAttitudesCanBeEmpiricallyAssociatedWithHostileDesignApproval : Bool
    ideologicalAttitudesCanBeEmpiricallyAssociatedWithHostileDesignApprovalIsTrue :
      ideologicalAttitudesCanBeEmpiricallyAssociatedWithHostileDesignApproval ≡ true
    politicalOrderingCanAffectPublicAffordances : Bool
    politicalOrderingCanAffectPublicAffordancesIsTrue :
      politicalOrderingCanAffectPublicAffordances ≡ true

canonicalPoliticalBoundary : PoliticalBoundary
canonicalPoliticalBoundary = politicalBoundary false refl true refl true refl

------------------------------------------------------------------------
-- British Columbia cross-pollination.
--
-- The existing BC owner already separates legal possession protection from
-- public-space protection, policing, services, housing and poverty reduction.
-- We expose only a thin phase-to-public-space-regime adapter here.
------------------------------------------------------------------------

bcPublicSpaceRegime : BC.PolicyPhase → InstitutionalRegime
bcPublicSpaceRegime BC.initialPilot = partialPermissionRegime
bcPublicSpaceRegime BC.postPublicSpaceAmendment = restrictiveRegime
bcPublicSpaceRegime BC.postExpiry = restrictiveRegime

bcAmendmentChangesPublicSpaceRegime :
  bcPublicSpaceRegime BC.initialPilot
    ≡ bcPublicSpaceRegime BC.postPublicSpaceAmendment → ⊥
bcAmendmentChangesPublicSpaceRegime ()

record BCToEcologyBridgeBoundary : Set where
  constructor bcToEcologyBridgeBoundary
  field
    decriminalizationLabelEqualsCompleteSupportiveEcology : Bool
    decriminalizationLabelEqualsCompleteSupportiveEcologyIsFalse :
      decriminalizationLabelEqualsCompleteSupportiveEcology ≡ false
    publicSpaceRuleIsSeparateEcologicalAxis : Bool
    publicSpaceRuleIsSeparateEcologicalAxisIsTrue :
      publicSpaceRuleIsSeparateEcologicalAxis ≡ true
    housingAndPovertyInfrastructureRemainSeparate : Bool
    housingAndPovertyInfrastructureRemainSeparateIsTrue :
      housingAndPovertyInfrastructureRemainSeparate ≡ true

canonicalBCToEcologyBridgeBoundary : BCToEcologyBridgeBoundary
canonicalBCToEcologyBridgeBoundary =
  bcToEcologyBridgeBoundary false refl true refl true refl

------------------------------------------------------------------------
-- Provenance handles.
------------------------------------------------------------------------

builtEnvironmentSource : Sources.SourceReference
builtEnvironmentSource = Sources.builtEnvironment2026

hostileDesignSource : Sources.SourceReference
hostileDesignSource = Sources.hostileDesign2024

supportiveHousingSource : Sources.SourceReference
supportiveHousingSource = Sources.supportiveHousing2023

thirdPlaceSource : Sources.SourceReference
thirdPlaceSource = Sources.oldenburg1989

socialEcologySource : Sources.SourceReference
socialEcologySource = Sources.bronfenbrenner1979

record SocialEcologicalAffordanceBoundary : Set where
  constructor socialEcologicalAffordanceBoundary
  field
    accessibilityIsPersonOnlyProperty : Bool
    accessibilityIsPersonOnlyPropertyIsFalse : accessibilityIsPersonOnlyProperty ≡ false
    nominalLegalPermissionEqualsRealizedEcologicalFreedom : Bool
    nominalLegalPermissionEqualsRealizedEcologicalFreedomIsFalse :
      nominalLegalPermissionEqualsRealizedEcologicalFreedom ≡ false
    safeSpaceEqualsSafeRelationship : Bool
    safeSpaceEqualsSafeRelationshipIsFalse : safeSpaceEqualsSafeRelationship ≡ false
    environmentalChangeCanAlterReachabilityWithoutChangingPerson : Bool
    environmentalChangeCanAlterReachabilityWithoutChangingPersonIsTrue :
      environmentalChangeCanAlterReachabilityWithoutChangingPerson ≡ true

canonicalSocialEcologicalAffordanceBoundary : SocialEcologicalAffordanceBoundary
canonicalSocialEcologicalAffordanceBoundary =
  socialEcologicalAffordanceBoundary false refl false refl false refl true refl
