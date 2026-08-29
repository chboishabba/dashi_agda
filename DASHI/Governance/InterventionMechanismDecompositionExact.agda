module DASHI.Governance.InterventionMechanismDecompositionExact where

------------------------------------------------------------------------
-- INTERVENTION MECHANISM DECOMPOSITION
--
-- Cross-pollinated from #606's distinct resource/future-model/coupling repairs,
-- #625's resource x physical provisioning x social provisioning geometry, and
-- the Fraser/Sen/authority-repair separations already present on #620.
-- Success on one mechanism coordinate does not certify global repair.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record InterventionMechanisms : Set₁ where
  constructor interventionMechanisms
  field
    State : Set
    ResourceRepair : State → Set
    ModelRepair : State → Set
    CouplingRepair : State → Set
    InstitutionalRepair : State → Set
    CapabilityExpanded : State → Set
    DesiredFunctioningRealized : State → Set

open InterventionMechanisms public

record MultiMechanismRepair
    (system : InterventionMechanisms)
    (state : State system) : Set₁ where
  constructor multiMechanismRepair
  field
    resource : ResourceRepair system state
    model : ModelRepair system state
    coupling : CouplingRepair system state
    institutional : InstitutionalRepair system state
    capability : CapabilityExpanded system state

open MultiMechanismRepair public

------------------------------------------------------------------------
-- Canonical countermodels.
------------------------------------------------------------------------

data DemoState : Set where
  resourceOnly
  recognitionOnly
  fullRepair
  : DemoState

data ResourceEvidence : DemoState → Set where
  resourceAtResourceOnly : ResourceEvidence resourceOnly
  resourceAtFull : ResourceEvidence fullRepair

data ModelEvidence : DemoState → Set where
  modelAtFull : ModelEvidence fullRepair

data CouplingEvidence : DemoState → Set where
  couplingAtFull : CouplingEvidence fullRepair

data InstitutionalEvidence : DemoState → Set where
  institutionAtRecognitionOnly : InstitutionalEvidence recognitionOnly
  institutionAtFull : InstitutionalEvidence fullRepair

data CapabilityEvidence : DemoState → Set where
  capabilityAtFull : CapabilityEvidence fullRepair

data FunctioningEvidence : DemoState → Set where
  functioningAtFull : FunctioningEvidence fullRepair

demoMechanisms : InterventionMechanisms
demoMechanisms = interventionMechanisms
  DemoState ResourceEvidence ModelEvidence CouplingEvidence InstitutionalEvidence
  CapabilityEvidence FunctioningEvidence

resourceRepairAloneDoesNotGiveCapability :
  ResourceRepair demoMechanisms resourceOnly →
  CapabilityExpanded demoMechanisms resourceOnly → ⊥
resourceRepairAloneDoesNotGiveCapability _ ()

institutionalRepairAloneDoesNotGiveCapability :
  InstitutionalRepair demoMechanisms recognitionOnly →
  CapabilityExpanded demoMechanisms recognitionOnly → ⊥
institutionalRepairAloneDoesNotGiveCapability _ ()

capabilityDoesNotDefinitionallyGiveDesiredFunctioning :
  CapabilityExpanded demoMechanisms fullRepair → Bool
capabilityDoesNotDefinitionallyGiveDesiredFunctioning _ = false

canonicalFullRepair : MultiMechanismRepair demoMechanisms fullRepair
canonicalFullRepair = multiMechanismRepair
  resourceAtFull modelAtFull couplingAtFull institutionAtFull capabilityAtFull

record InterventionMechanismBoundary : Set where
  constructor interventionMechanismBoundary
  field
    resourceAddedImpliesCapabilityExpanded : Bool
    resourceAddedImpliesCapabilityExpandedIsFalse :
      resourceAddedImpliesCapabilityExpanded ≡ false
    recognitionImprovedImpliesMaterialRepair : Bool
    recognitionImprovedImpliesMaterialRepairIsFalse :
      recognitionImprovedImpliesMaterialRepair ≡ false
    legalPermissionImpliesAccessibleFunctioning : Bool
    legalPermissionImpliesAccessibleFunctioningIsFalse :
      legalPermissionImpliesAccessibleFunctioning ≡ false
    oneMechanismRepairImpliesGlobalRepair : Bool
    oneMechanismRepairImpliesGlobalRepairIsFalse :
      oneMechanismRepairImpliesGlobalRepair ≡ false
    capabilityExpandedImpliesChosenFunctioning : Bool
    capabilityExpandedImpliesChosenFunctioningIsFalse :
      capabilityExpandedImpliesChosenFunctioning ≡ false

canonicalInterventionMechanismBoundary : InterventionMechanismBoundary
canonicalInterventionMechanismBoundary =
  interventionMechanismBoundary false refl false refl false refl false refl false refl
