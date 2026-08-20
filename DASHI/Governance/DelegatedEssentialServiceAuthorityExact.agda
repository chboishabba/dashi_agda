module DASHI.Governance.DelegatedEssentialServiceAuthorityExact where

------------------------------------------------------------------------
-- DELEGATED ESSENTIAL-SERVICE AUTHORITY
--
-- Existing repository law is reused, not replaced:
--   HealthcareEqualityInvariant
--   HealthcareAccessDistortion
--   PublicEssentialCareDoctrineBoundary
--
-- Those modules already prove that clinically equivalent need with unequal
-- accessible care destroys the strict healthcare-equality predicate, and that
-- geography, institutional doctrine, provider identity, coloniality and
-- forced dependency are explanatory axes rather than excuses.
--
-- This module extracts the domain-neutral institutional topology needed for
-- schools, healthcare, out-of-home care and other essential-service systems.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Governance.HealthcareEqualityInvariant as Equality
import DASHI.Governance.HealthcareAccessDistortion as Distortion
import DASHI.Governance.PublicEssentialCareDoctrineBoundary as Care
import DASHI.Governance.EffectiveInstitutionalChoiceExact as Choice

------------------------------------------------------------------------
-- Public/delegated authority can be exercised through a non-state provider.
------------------------------------------------------------------------

data ServiceDomain : Set where
  educationService healthcareService outOfHomeCareService counsellingService : ServiceDomain
  housingService disabilityService detentionAdministrationService : ServiceDomain

data ProviderGovernance : Set where
  publicProvider privateProvider religiousProvider communityControlledProvider : ProviderGovernance

data DelegationSurface : Set where
  noDelegation publicFunding publicContract statutoryPlacement publicReferral : DelegationSurface

data Essentiality : Set where
  optional important essential lifePreserving : Essentiality

record DelegatedServiceProvider : Set where
  constructor delegatedServiceProvider
  field
    domain : ServiceDomain
    governance : ProviderGovernance
    delegation : DelegationSurface
    essentiality : Essentiality
    publiclyFunded : Bool
    institutionalDoctrineOperative : Bool
    effectiveAlternativeAvailable : Bool
    subjectExitCost : Nat

open DelegatedServiceProvider public

data EssentialOrLifePreserving : Essentiality → Set where
  essentialWitness : EssentialOrLifePreserving essential
  lifePreservingWitness : EssentialOrLifePreserving lifePreserving

------------------------------------------------------------------------
-- Dependency does not require physical confinement.  It can arise because a
-- service is essential and no effectively accessible substitute is available.
------------------------------------------------------------------------

record EffectiveProviderDependency (provider : DelegatedServiceProvider) : Set where
  constructor effectiveProviderDependency
  field
    criticalityWitness : EssentialOrLifePreserving (essentiality provider)
    noAlternativeWitness : effectiveAlternativeAvailable provider ≡ false

open EffectiveProviderDependency public

data ReligiousProviderPromotesCoercion : Set where

data PublicFundingPromotesLegitimacy : Set where

data ProviderDependencyPromotesEntrapment : Set where

religiousProviderDoesNotPromoteCoercion : ReligiousProviderPromotesCoercion → ⊥
religiousProviderDoesNotPromoteCoercion ()

publicFundingDoesNotPromoteLegitimacy : PublicFundingPromotesLegitimacy → ⊥
publicFundingDoesNotPromoteLegitimacy ()

dependencyDoesNotPromoteEntrapment : ProviderDependencyPromotesEntrapment → ⊥
dependencyDoesNotPromoteEntrapment ()

------------------------------------------------------------------------
-- Direct healthcare cross-pollination: the pre-existing theorem remains the
-- stronger domain-specific consumer whenever we actually possess a clinical
-- access-divergence witness.
------------------------------------------------------------------------

healthcareDoctrinalFailureStillDestroysEquality :
  ∀ {Patient Need CareType}
    {system : Equality.HealthcareSystem Patient Need CareType} →
  Care.PublicDoctrineAccessFailure system →
  Equality.HealthcareEquality system →
  Equality.Never
healthcareDoctrinalFailureStillDestroysEquality =
  Care.publicDoctrineAccessFailureDestroysEquality

doctrineIsExistingAccessDistortionAxis : Distortion.DistortionAxis
doctrineIsExistingAccessDistortionAxis = Distortion.institutionalDoctrine

colonialityIsExistingAccessDistortionAxis : Distortion.DistortionAxis
colonialityIsExistingAccessDistortionAxis = Distortion.raceOrColoniality

forcedDependencyIsExistingAccessDistortionAxis : Distortion.DistortionAxis
forcedDependencyIsExistingAccessDistortionAxis = Distortion.forcedDependency

record DelegatedEssentialServiceBoundary : Set where
  constructor delegatedEssentialServiceBoundary
  field
    nonStateProviderCanParticipateInDelegatedSystem : Bool
    effectiveDependencyRequiresPhysicalConfinement : Bool
    religiousOwnershipEqualsDoctrinalAccessFailure : Bool
    doctrineCanBeAccessDistortionWhenDivergenceWitnessed : Bool
    publicFundingEqualsNormativeApproval : Bool
    effectiveDependencyEqualsEntrapment : Bool
    healthcareStrictEqualityReused : Bool

canonicalDelegatedEssentialServiceBoundary : DelegatedEssentialServiceBoundary
canonicalDelegatedEssentialServiceBoundary =
  delegatedEssentialServiceBoundary true false false true false false true
