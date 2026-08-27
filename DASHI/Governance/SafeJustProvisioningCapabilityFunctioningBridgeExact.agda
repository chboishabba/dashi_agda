module DASHI.Governance.SafeJustProvisioningCapabilityFunctioningBridgeExact where

open import DASHI.Core.Prelude
import DASHI.Governance.ProvisioningGeometryExact as Provisioning

------------------------------------------------------------------------
-- SAFE/JUST PROVISIONING -> CAPABILITY -> FUNCTIONING
--
-- Thin domain bridge.  It deliberately does not import draft PR #620.  Its
-- theorem shape is intended to become an adapter to the generic
-- InterventionMechanismDecompositionExact / CapabilityFunctioningNonDescentExact
-- owners after ancestry reconciliation.
--
-- Source calibration remains O'Neill et al. 2018 through ProvisioningGeometry.
-- The capability/functioning separation is a DASHI formal bridge, motivated by
-- the established capability-approach distinction rather than attributed to the
-- O'Neill paper as a theorem of that source.
------------------------------------------------------------------------

data CapabilitySurface : Set where
  restrictedCapability broadCapability : CapabilitySurface

data Functioning : Set where
  unmetFunctioning metFunctioning : Functioning

record ProvisionedLifeState : Set where
  constructor provisionedLifeState
  field
    resources : Provisioning.ResourceLevel
    provisioning : Provisioning.ProvisioningSystem
    capability : CapabilitySurface
    functioning : Functioning

open ProvisionedLifeState public

------------------------------------------------------------------------
-- Three finite interventions separate input, conversion, capability and result.
------------------------------------------------------------------------

baseline : ProvisionedLifeState
baseline = provisionedLifeState
  Provisioning.lowResource
  (Provisioning.provisioningSystem
    Provisioning.inefficientInfrastructure
    Provisioning.exclusionaryProvisioning)
  restrictedCapability
  unmetFunctioning

resourceOnly : ProvisionedLifeState
resourceOnly = provisionedLifeState
  Provisioning.highResource
  (Provisioning.provisioningSystem
    Provisioning.inefficientInfrastructure
    Provisioning.exclusionaryProvisioning)
  restrictedCapability
  unmetFunctioning

provisioningRepair : ProvisionedLifeState
provisioningRepair = provisionedLifeState
  Provisioning.mediumResource
  (Provisioning.provisioningSystem
    Provisioning.efficientInfrastructure
    Provisioning.inclusiveProvisioning)
  broadCapability
  metFunctioning

sameFunctioningDifferentCapabilityLeft : ProvisionedLifeState
sameFunctioningDifferentCapabilityLeft = provisionedLifeState
  Provisioning.lowResource
  (Provisioning.provisioningSystem
    Provisioning.efficientInfrastructure
    Provisioning.inclusiveProvisioning)
  broadCapability
  metFunctioning

sameFunctioningDifferentCapabilityRight : ProvisionedLifeState
sameFunctioningDifferentCapabilityRight = provisionedLifeState
  Provisioning.highResource
  (Provisioning.provisioningSystem
    Provisioning.inefficientInfrastructure
    Provisioning.exclusionaryProvisioning)
  restrictedCapability
  metFunctioning

resourceInputChanged : resources baseline ≡ resources resourceOnly → ⊥
resourceInputChanged ()

resourceOnlyCapabilityUnchanged :
  capability baseline ≡ capability resourceOnly
resourceOnlyCapabilityUnchanged = refl

resourceOnlyFunctioningUnchanged :
  functioning baseline ≡ functioning resourceOnly
resourceOnlyFunctioningUnchanged = refl

provisioningRepairCapabilityChanged :
  capability baseline ≡ capability provisioningRepair → ⊥
provisioningRepairCapabilityChanged ()

provisioningRepairFunctioningChanged :
  functioning baseline ≡ functioning provisioningRepair → ⊥
provisioningRepairFunctioningChanged ()

sameFunctioning :
  functioning sameFunctioningDifferentCapabilityLeft ≡
  functioning sameFunctioningDifferentCapabilityRight
sameFunctioning = refl

sameFunctioningDoesNotRecoverCapability :
  capability sameFunctioningDifferentCapabilityLeft ≡
  capability sameFunctioningDifferentCapabilityRight → ⊥
sameFunctioningDoesNotRecoverCapability ()

record SafeJustCapabilityFunctioningBoundary : Set where
  constructor safeJustCapabilityFunctioningBoundary
  field
    moreResourcesAloneGuaranteeCapabilityExpansion : Bool
    moreResourcesAloneGuaranteeCapabilityExpansionIsFalse :
      moreResourcesAloneGuaranteeCapabilityExpansion ≡ false
    moreResourcesAloneGuaranteeImprovedFunctioning : Bool
    moreResourcesAloneGuaranteeImprovedFunctioningIsFalse :
      moreResourcesAloneGuaranteeImprovedFunctioning ≡ false
    sameFunctioningDeterminesCapabilitySurface : Bool
    sameFunctioningDeterminesCapabilitySurfaceIsFalse :
      sameFunctioningDeterminesCapabilitySurface ≡ false
    capabilitySurfaceIsIdenticalToFunctioning : Bool
    capabilitySurfaceIsIdenticalToFunctioningIsFalse :
      capabilitySurfaceIsIdenticalToFunctioning ≡ false
    finiteBridgeIsEmpiricalCausalModel : Bool
    finiteBridgeIsEmpiricalCausalModelIsFalse :
      finiteBridgeIsEmpiricalCausalModel ≡ false

canonicalSafeJustCapabilityFunctioningBoundary :
  SafeJustCapabilityFunctioningBoundary
canonicalSafeJustCapabilityFunctioningBoundary =
  safeJustCapabilityFunctioningBoundary
    false refl false refl false refl false refl false refl
