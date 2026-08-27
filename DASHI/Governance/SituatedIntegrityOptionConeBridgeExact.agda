module DASHI.Governance.SituatedIntegrityOptionConeBridgeExact where

------------------------------------------------------------------------
-- SITUATED INTEGRITY -> OPTION-CONE BRIDGE
--
-- This is the generic seam requested by the social-ecology / Solis thread.
-- `DeclaredRealizedIntegrityResidualExact` already proves that the same person
-- and the same nominal public-access declaration can yield different realised
-- access across environments.  `OptionConeCoercionExact` already owns the
-- proof-bearing safe-option-cone interface.
--
-- This module composes those owners and proves the stronger exact statement:
--
--   same person + same declared public access
--   + different realised ecology
--   -> strict contraction of a declared reachable option cone.
--
-- The contraction is a comparison theorem.  It does not assert that one
-- environment is the dynamical successor of the other, that the contraction is
-- coercion, or that a mismatch proves hostile intent.
--
-- Cross-PR calibration (not imported):
--   * PR #618 has the richer neurodivergent social-ecology cone and trusted-
--     friend relation surfaces;
--   * PR #606 owns world/perceived/accessible/actionable subfabrics;
--   * PR #624 uses the same option-cone grammar for trading action viability.
-- Once ancestry is reconciled those lanes should consume this generic seam
-- rather than duplicate it.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Empty using (⊥-elim)

import DASHI.Core.DeclaredRealizedIntegrityResidualExact as Integrity
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Governance.OptionConeCoercionExact as Cone

------------------------------------------------------------------------
-- One social-ecological option: being able to remain in the public setting.
------------------------------------------------------------------------

data SituatedOption : Set where
  remainInPlace : SituatedOption

data SituatedAvailable :
  Integrity.PublicEnvironment → SituatedOption → Set where
  thirdPlaceRemain :
    SituatedAvailable Integrity.lowDemandThirdPlace remainInPlace

situatedOptionCone :
  Cone.SafeReachabilitySystem Integrity.PublicEnvironment SituatedOption
situatedOptionCone = Cone.safeReachabilitySystem SituatedAvailable

remainAvailableInThirdPlace :
  Cone.Available
    situatedOptionCone
    Integrity.lowDemandThirdPlace
    remainInPlace
remainAvailableInThirdPlace = thirdPlaceRemain

remainUnavailableInRestrictedSpace :
  Cone.Available
    situatedOptionCone
    Integrity.highDemandRestrictedSpace
    remainInPlace → ⊥
remainUnavailableInRestrictedSpace ()

restrictedConeIncludedInThirdPlaceCone :
  (option : SituatedOption) →
  Cone.Available situatedOptionCone Integrity.highDemandRestrictedSpace option →
  Cone.Available situatedOptionCone Integrity.lowDemandThirdPlace option
restrictedConeIncludedInThirdPlaceCone remainInPlace impossible =
  ⊥-elim (remainUnavailableInRestrictedSpace impossible)

canonicalSituatedOptionConeContraction :
  Cone.StrictSafeReachabilityContraction
    situatedOptionCone
    Integrity.lowDemandThirdPlace
    Integrity.highDemandRestrictedSpace
canonicalSituatedOptionConeContraction =
  Cone.strictSafeReachabilityContraction
    restrictedConeIncludedInThirdPlaceCone
    remainInPlace
    remainAvailableInThirdPlace
    remainUnavailableInRestrictedSpace

------------------------------------------------------------------------
-- The nominal declaration remains identical across the comparison.
------------------------------------------------------------------------

declaredOnlyObserver : Integrity.PublicEnvironment → Integrity.DeclaredAccess
declaredOnlyObserver environment =
  Integrity.declaredObservation Integrity.publicAccessObserver environment

sameDeclaredPublicAccess :
  declaredOnlyObserver Integrity.lowDemandThirdPlace
  ≡ declaredOnlyObserver Integrity.highDemandRestrictedSpace
sameDeclaredPublicAccess = refl

remainAvailabilityCode : Integrity.PublicEnvironment → Bool
remainAvailabilityCode Integrity.lowDemandThirdPlace = true
remainAvailabilityCode Integrity.highDemandRestrictedSpace = false

remainCodesDiffer :
  remainAvailabilityCode Integrity.lowDemandThirdPlace
  ≡ remainAvailabilityCode Integrity.highDemandRestrictedSpace → ⊥
remainCodesDiffer ()

declaredAccessCannotRecoverRemainAvailability :
  NF.NonFactorabilityWitness declaredOnlyObserver remainAvailabilityCode
declaredAccessCannotRecoverRemainAvailability =
  NF.nonFactorabilityWitness
    Integrity.lowDemandThirdPlace
    Integrity.highDemandRestrictedSpace
    sameDeclaredPublicAccess
    remainCodesDiffer

noDeclaredAccessOnlyRemainClassifier :
  NF.FactorsThrough declaredOnlyObserver remainAvailabilityCode → ⊥
noDeclaredAccessOnlyRemainClassifier =
  NF.witnessRulesOutEveryFlatFactorisation
    declaredAccessCannotRecoverRemainAvailability

postprocessedDeclarationStillCannotRecoverRemainAvailability :
  ∀ {Chart : Set} →
  (rechart : Integrity.DeclaredAccess → Chart) →
  NF.FactorsThrough
    (λ environment → rechart (declaredOnlyObserver environment))
    remainAvailabilityCode →
  ⊥
postprocessedDeclarationStillCannotRecoverRemainAvailability rechart =
  NF.rechartingCannotRecoverErasedPhenomenon
    rechart declaredAccessCannotRecoverRemainAvailability

------------------------------------------------------------------------
-- Keep option-cone contraction distinct from coercion and causal transition.
------------------------------------------------------------------------

record SituatedIntegrityOptionConeBoundary : Set where
  constructor situated-integrity-option-cone-boundary
  field
    sameDeclaredAccessImpliesSameOptionCone : Bool
    sameDeclaredAccessImpliesSameOptionConeIsFalse :
      sameDeclaredAccessImpliesSameOptionCone ≡ false
    optionConeContractionAloneProvesCoercion : Bool
    optionConeContractionAloneProvesCoercionIsFalse :
      optionConeContractionAloneProvesCoercion ≡ false
    comparisonClaimsActualEnvironmentTransition : Bool
    comparisonClaimsActualEnvironmentTransitionIsFalse :
      comparisonClaimsActualEnvironmentTransition ≡ false
    mismatchProvesHostileIntent : Bool
    mismatchProvesHostileIntentIsFalse : mismatchProvesHostileIntent ≡ false
    environmentCanChangeRealizedCapabilityWithoutChangingPerson : Bool
    environmentCanChangeRealizedCapabilityWithoutChangingPersonIsTrue :
      environmentCanChangeRealizedCapabilityWithoutChangingPerson ≡ true

canonicalSituatedIntegrityOptionConeBoundary :
  SituatedIntegrityOptionConeBoundary
canonicalSituatedIntegrityOptionConeBoundary =
  situated-integrity-option-cone-boundary
    false refl
    false refl
    false refl
    false refl
    true refl
