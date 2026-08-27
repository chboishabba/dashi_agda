module DASHI.Governance.ProvisioningGeometryExact where

open import DASHI.Core.Prelude
open import DASHI.Governance.SafeJustSourceRegistryExact as Sources

------------------------------------------------------------------------
-- ENDS-MEANS / PROVISIONING GEOMETRY
--
-- The 2018 framework places physical and social provisioning between resource
-- use and need satisfaction.  This finite owner makes that intermediary
-- explicit and gives exact counterexamples to resource-only determination.
------------------------------------------------------------------------

data ResourceLevel : Set where
  lowResource mediumResource highResource : ResourceLevel

data PhysicalProvisioning : Set where
  inefficientInfrastructure efficientInfrastructure : PhysicalProvisioning

data SocialProvisioning : Set where
  exclusionaryProvisioning inclusiveProvisioning : SocialProvisioning

data NeedOutcome : Set where
  unmetNeed metNeed : NeedOutcome

record ProvisioningSystem : Set where
  constructor provisioningSystem
  field
    physical : PhysicalProvisioning
    social : SocialProvisioning

open ProvisioningSystem public

record ProvisioningState : Set where
  constructor provisioningState
  field
    resources : ResourceLevel
    system : ProvisioningSystem

open ProvisioningState public

realizedNeed : ProvisioningState → NeedOutcome
realizedNeed (provisioningState lowResource (provisioningSystem efficientInfrastructure inclusiveProvisioning)) = metNeed
realizedNeed (provisioningState mediumResource (provisioningSystem efficientInfrastructure inclusiveProvisioning)) = metNeed
realizedNeed (provisioningState highResource (provisioningSystem inefficientInfrastructure exclusionaryProvisioning)) = unmetNeed
realizedNeed _ = unmetNeed

sameResourceBad : ProvisioningState
sameResourceBad = provisioningState mediumResource (provisioningSystem inefficientInfrastructure exclusionaryProvisioning)

sameResourceGood : ProvisioningState
sameResourceGood = provisioningState mediumResource (provisioningSystem efficientInfrastructure inclusiveProvisioning)

sameResource : resources sameResourceBad ≡ resources sameResourceGood
sameResource = refl

sameResourceDifferentOutcome : realizedNeed sameResourceBad ≡ realizedNeed sameResourceGood → ⊥
sameResourceDifferentOutcome ()

lowEfficient : ProvisioningState
lowEfficient = provisioningState lowResource (provisioningSystem efficientInfrastructure inclusiveProvisioning)

mediumEfficient : ProvisioningState
mediumEfficient = provisioningState mediumResource (provisioningSystem efficientInfrastructure inclusiveProvisioning)

sameOutcomeDifferentResource : realizedNeed lowEfficient ≡ realizedNeed mediumEfficient
sameOutcomeDifferentResource = refl

resourceDifferenceRemains : resources lowEfficient ≡ resources mediumEfficient → ⊥
resourceDifferenceRemains ()

------------------------------------------------------------------------
-- The observed best-versus-typical resource gap is typed only as an observed
-- residual.  It is not promoted into an identified causal treatment effect of
-- provisioning institutions.
------------------------------------------------------------------------

record ObservedProvisioningResidual : Set where
  constructor observedProvisioningResidual
  field
    typicalResourceCode : Nat
    lowerObservedResourceCode : Nat
    lowerObservedNoGreater : lowerObservedResourceCode ≤ typicalResourceCode

canonicalResidual : ObservedProvisioningResidual
canonicalResidual = observedProvisioningResidual 3 1 (s≤s z≤n)

data IdentifiedProvisioningTreatmentEffect : Set where

observedResidualDoesNotSupplyTreatmentIdentification :
  IdentifiedProvisioningTreatmentEffect → ⊥
observedResidualDoesNotSupplyTreatmentIdentification ()

source : Sources.SourceReference
source = Sources.oneill2018

record ProvisioningBoundary : Set where
  constructor provisioningBoundary
  field
    resourceQuantityAloneDeterminesNeedOutcome : Bool
    resourceQuantityAloneDeterminesNeedOutcomeIsFalse :
      resourceQuantityAloneDeterminesNeedOutcome ≡ false
    equalOutcomeImpliesEqualResourceUse : Bool
    equalOutcomeImpliesEqualResourceUseIsFalse : equalOutcomeImpliesEqualResourceUse ≡ false
    observedEfficiencyGapIsIdentifiedCausalEffect : Bool
    observedEfficiencyGapIsIdentifiedCausalEffectIsFalse :
      observedEfficiencyGapIsIdentifiedCausalEffect ≡ false

canonicalProvisioningBoundary : ProvisioningBoundary
canonicalProvisioningBoundary = provisioningBoundary false refl false refl false refl
