module DASHI.Physics.Closure.CounterfactualPhysicalRealisationBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AdmissibleCounterfactualWorldFamilyExact as Counterfactual
import DASHI.Physics.Closure.TSFVMultiverseViabilityCrossPollinationExact as TSFV
import DASHI.Physics.Foundations.TSFVFeynmanDerivationObligationsExact as Feynman

------------------------------------------------------------------------
-- COUNTERFACTUAL / PHYSICAL REALISATION BRIDGE
--
-- Cross-domain firewall only.  Legal, policy and historical counterfactuals do
-- not inherit physical admissibility by declaration.  Conversely a mathematically
-- viable physical parameter/history does not become an actual-world causal
-- alternative without the relevant physical realisation/model receipts.
------------------------------------------------------------------------

data PhysicalCompatibilityStatus : Set where
  physicallyCompatible
  physicallyIncompatible
  physicalCompatibilityUnresolved
  : PhysicalCompatibilityStatus

data PhysicalRealisationStatus : Set where
  realisedByAcceptedPhysicalModel
  counterfactualPhysicalModelOnly
  physicalRealisationUnresolved
  : PhysicalRealisationStatus

record CounterfactualPhysicalWeld : Set where
  constructor counterfactual-physical-weld
  field
    legalOrDomainWorldReference : String
    physicalModelReference : String
    boundaryConditionReference : String
    conservationOrConstraintReference : String
    empiricalCalibrationReference : String
    compatibility : PhysicalCompatibilityStatus
    realisation : PhysicalRealisationStatus
    physicalModelAdequacyReceipt : Set
    boundaryConditionReceipt : Set
    calibrationReceipt : Set
    legalAdmissibilityNotUsedAsPhysicsProof : Bool
    legalAdmissibilityNotUsedAsPhysicsProofIsTrue :
      legalAdmissibilityNotUsedAsPhysicsProof ≡ true
    physicalModelNotUsedAsLegalAuthority : Bool
    physicalModelNotUsedAsLegalAuthorityIsTrue :
      physicalModelNotUsedAsLegalAuthority ≡ true

open CounterfactualPhysicalWeld public

------------------------------------------------------------------------
-- TSFV/multiverse boundaries remain upstream constraints.
------------------------------------------------------------------------

tsfvBoundary : TSFV.TSFVMultiverseViabilityBoundary
tsfvBoundary = TSFV.canonicalTSFVMultiverseViabilityBoundary

parameterPointIsNotAutomaticallyRealisedUniverse :
  TSFV.parameterSpacePointIsAutomaticallyRealisedUniverse tsfvBoundary ≡ false
parameterPointIsNotAutomaticallyRealisedUniverse = refl

viableParameterRegionDoesNotProveMultiverse :
  TSFV.viableParameterRegionProvesMultiverse tsfvBoundary ≡ false
viableParameterRegionDoesNotProveMultiverse = refl

------------------------------------------------------------------------
-- Domain-independent counterfactual boundary remains distinct from physics.
------------------------------------------------------------------------

counterfactualBoundary : Counterfactual.AdmissibleCounterfactualBoundary
counterfactualBoundary = Counterfactual.canonicalAdmissibleCounterfactualBoundary

legalAdmissibilityDoesNotEqualPhysicalRealisation :
  Counterfactual.legalAdmissibilityEqualsPhysicalRealisation counterfactualBoundary ≡ false
legalAdmissibilityDoesNotEqualPhysicalRealisation = refl

------------------------------------------------------------------------
-- Physics can test factual premises without acquiring legal authority.
------------------------------------------------------------------------

data PhysicalCausalSupport : Set where physicalCausalSupport : PhysicalCausalSupport
data LegalLiabilityAuthority : Set where legalLiabilityAuthority : LegalLiabilityAuthority
data PhysicalTestAutomaticallySuppliesLegalLiability : Set where

physicalTestDoesNotAutoSupplyLegalLiability :
  PhysicalTestAutomaticallySuppliesLegalLiability → ⊥
physicalTestDoesNotAutoSupplyLegalLiability ()

record PhysicalCounterfactualTestingBoundary : Set where
  constructor physical-counterfactual-testing-boundary
  field
    physicalLawMayExcludeCandidateWorld : Bool
    physicalLawMayExcludeCandidateWorldIsTrue :
      physicalLawMayExcludeCandidateWorld ≡ true
    experimentMayDiscriminateCandidateWorlds : Bool
    experimentMayDiscriminateCandidateWorldsIsTrue :
      experimentMayDiscriminateCandidateWorlds ≡ true
    physicalExclusionEstablishesLegalLiability : Bool
    physicalExclusionEstablishesLegalLiabilityIsFalse :
      physicalExclusionEstablishesLegalLiability ≡ false
    physicalModelAdequacyEstablishesLegalLegitimacy : Bool
    physicalModelAdequacyEstablishesLegalLegitimacyIsFalse :
      physicalModelAdequacyEstablishesLegalLegitimacy ≡ false
    legalNormSelectsPhysicalReality : Bool
    legalNormSelectsPhysicalRealityIsFalse : legalNormSelectsPhysicalReality ≡ false

canonicalPhysicalCounterfactualTestingBoundary : PhysicalCounterfactualTestingBoundary
canonicalPhysicalCounterfactualTestingBoundary =
  physical-counterfactual-testing-boundary
    true refl
    true refl
    false refl
    false refl
    false refl
