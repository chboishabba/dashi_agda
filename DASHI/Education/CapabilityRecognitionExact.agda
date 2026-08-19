module DASHI.Education.CapabilityRecognitionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NonFactor

------------------------------------------------------------------------
-- CAPABILITY != REACHABILITY != SOCIAL LEGIBILITY != RECOGNITION
--
-- A strength-based intervention may expose and recognise a capability that was
-- already present.  Therefore observed contribution is not a safe deficit
-- detector, and institutional recognition is not the source of all capability.
------------------------------------------------------------------------

record CapabilityRecognitionState : Set where
  constructor capabilityRecognitionState
  field
    capabilityPresent : Bool
    enactmentReachable : Bool
    contributionLegible : Bool
    contributionRecognised : Bool
    actorCanDecline : Bool
    institutionalAuthorityAdded : Bool
    receipt : String

open CapabilityRecognitionState public

latentUnrecognised : CapabilityRecognitionState
latentUnrecognised =
  capabilityRecognitionState
    true false false false true false
    "capability is already present but has no currently reachable or socially legible contribution route"

reachableRecognised : CapabilityRecognitionState
reachableRecognised =
  capabilityRecognitionState
    true true true true true false
    "same underlying capability becomes reachable, visible and recognised without manufacturing institutional authority"

absentUnrecognised : CapabilityRecognitionState
absentUnrecognised =
  capabilityRecognitionState
    false false false false true false
    "capability absent in this finite countermodel; recognition is also absent"

capabilityProjection : CapabilityRecognitionState → Bool
capabilityProjection = capabilityPresent

recognitionProjection : CapabilityRecognitionState → Bool
recognitionProjection = contributionRecognised

reachabilityProjection : CapabilityRecognitionState → Bool
reachabilityProjection = enactmentReachable

legibilityProjection : CapabilityRecognitionState → Bool
legibilityProjection = contributionLegible

sameCapabilityDifferentRecognition :
  capabilityProjection latentUnrecognised ≡ capabilityProjection reachableRecognised
sameCapabilityDifferentRecognition = refl

recognitionDiffersAtSameCapability :
  recognitionProjection latentUnrecognised ≡ recognitionProjection reachableRecognised → ⊥
recognitionDiffersAtSameCapability ()

capabilityDoesNotDetermineRecognitionWitness :
  NonFactor.NonFactorabilityWitness capabilityProjection recognitionProjection
capabilityDoesNotDetermineRecognitionWitness =
  NonFactor.nonFactorabilityWitness
    latentUnrecognised reachableRecognised
    sameCapabilityDifferentRecognition recognitionDiffersAtSameCapability

capabilityAloneCannotDetermineRecognition :
  NonFactor.FactorsThrough capabilityProjection recognitionProjection → ⊥
capabilityAloneCannotDetermineRecognition =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    capabilityDoesNotDetermineRecognitionWitness

sameNonRecognitionDifferentCapability :
  recognitionProjection absentUnrecognised ≡ recognitionProjection latentUnrecognised
sameNonRecognitionDifferentCapability = refl

capabilityDiffersAtSameNonRecognition :
  capabilityProjection absentUnrecognised ≡ capabilityProjection latentUnrecognised → ⊥
capabilityDiffersAtSameNonRecognition ()

nonRecognitionDoesNotDetermineCapabilityWitness :
  NonFactor.NonFactorabilityWitness recognitionProjection capabilityProjection
nonRecognitionDoesNotDetermineCapabilityWitness =
  NonFactor.nonFactorabilityWitness
    absentUnrecognised latentUnrecognised
    sameNonRecognitionDifferentCapability capabilityDiffersAtSameNonRecognition

lackOfRecognitionCannotDetermineLackOfCapability :
  NonFactor.FactorsThrough recognitionProjection capabilityProjection → ⊥
lackOfRecognitionCannotDetermineLackOfCapability =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    nonRecognitionDoesNotDetermineCapabilityWitness

------------------------------------------------------------------------
-- Exact strength-based transition witness.
------------------------------------------------------------------------

record StrengthBasedRecognitionTransition
    (before after : CapabilityRecognitionState) : Set where
  constructor strengthBasedRecognitionTransition
  field
    capabilityPreserved : capabilityPresent before ≡ capabilityPresent after
    preExistingCapability : capabilityPresent before ≡ true
    previouslyBlocked : enactmentReachable before ≡ false
    routeOpened : enactmentReachable after ≡ true
    previouslyUnrecognised : contributionRecognised before ≡ false
    recognitionOpened : contributionRecognised after ≡ true
    declineRoutePreserved : actorCanDecline after ≡ true
    noAuthorityManufactured : institutionalAuthorityAdded after ≡ false

open StrengthBasedRecognitionTransition public

mulchingShapeTransition :
  StrengthBasedRecognitionTransition latentUnrecognised reachableRecognised
mulchingShapeTransition =
  strengthBasedRecognitionTransition refl refl refl refl refl refl refl refl

------------------------------------------------------------------------
-- Promotion boundaries.
------------------------------------------------------------------------

data RecognitionEqualsCapabilityPermission : Set where
data InstitutionCreatedAllCapabilityPermission : Set where
data RecognitionEqualsEmpowermentPermission : Set where

recognitionCannotAutoPromoteToCapabilityIdentity :
  RecognitionEqualsCapabilityPermission → ⊥
recognitionCannotAutoPromoteToCapabilityIdentity ()

institutionCannotAutoClaimToHaveCreatedExistingCapability :
  InstitutionCreatedAllCapabilityPermission → ⊥
institutionCannotAutoClaimToHaveCreatedExistingCapability ()

recognitionCannotAutoPromoteToWholeEmpowermentClaim :
  RecognitionEqualsEmpowermentPermission → ⊥
recognitionCannotAutoPromoteToWholeEmpowermentClaim ()

record CapabilityRecognitionBoundary : Set where
  constructor capabilityRecognitionBoundary
  field
    unrealisedContributionProvesDeficit : Bool
    recognitionCanChangeWhileCapabilityIsFixed : Bool
    nonRecognitionCanHideExistingCapability : Bool
    strengthBasedTransitionCanOpenRouteWithoutAddingAuthority : Bool
    recognitionAloneProvesEmpowerment : Bool

canonicalCapabilityRecognitionBoundary : CapabilityRecognitionBoundary
canonicalCapabilityRecognitionBoundary =
  capabilityRecognitionBoundary false true true true false
