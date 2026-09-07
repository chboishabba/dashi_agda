module DASHI.Physics.Closure.CounterfactualPhysicalRealisationBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.CounterfactualModelContractExact as Counterfactual
import DASHI.Core.CounterfactualRealisedRepairExact as Repair
import DASHI.Physics.Closure.TSFVMultiverseViabilityCrossPollinationExact as TSFV
import DASHI.Physics.Foundations.TSFVFeynmanDerivationObligationsExact as Feynman

------------------------------------------------------------------------
-- COUNTERFACTUAL / PHYSICAL REALISATION BRIDGE
--
-- Stacked on the canonical realised-repair owner from #794.  This file does not
-- introduce a parallel counterfactual ontology and does not import legal but-for
-- doctrine.  It adds a physical admissibility/realisation fibre for consumers
-- whose causal premises depend on physics, engineering, medicine, climate, etc.
--
-- Cross-domain discipline:
--   * domain/legal admissibility != physical compatibility;
--   * mathematical/theory viability != actual-world realisation;
--   * physical law may rule out a proposed corrected world;
--   * experiment may discriminate live corrected worlds;
--   * physical adequacy does not create legal liability, legitimacy, remedy or
--     authority.
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

record CounterfactualPhysicalWeld : Set₁ where
  constructor counterfactual-physical-weld
  field
    repairContract : Repair.RealisedRepairCounterfactualContract
    candidateWorldReference : String
    physicalModelReference : String
    boundaryConditionReference : String
    conservationOrConstraintReference : String
    empiricalCalibrationReference : String
    compatibility : PhysicalCompatibilityStatus
    realisation : PhysicalRealisationStatus
    physicalModelAdequacyReceipt : Set
    boundaryConditionReceipt : Set
    calibrationReceipt : Set
    domainAdmissibilityNotUsedAsPhysicsProof : Bool
    domainAdmissibilityNotUsedAsPhysicsProofIsTrue :
      domainAdmissibilityNotUsedAsPhysicsProof ≡ true
    physicalModelNotUsedAsLegalAuthority : Bool
    physicalModelNotUsedAsLegalAuthorityIsTrue :
      physicalModelNotUsedAsLegalAuthority ≡ true
    physicalModelNotUsedAsPoliticalLegitimacy : Bool
    physicalModelNotUsedAsPoliticalLegitimacyIsTrue :
      physicalModelNotUsedAsPoliticalLegitimacy ≡ true

open CounterfactualPhysicalWeld public

------------------------------------------------------------------------
-- Canonical upstream boundaries remain visible.
------------------------------------------------------------------------

counterfactualBoundary : Counterfactual.CounterfactualBoundary
counterfactualBoundary = Counterfactual.canonicalCounterfactualBoundary

repairBoundary : Repair.CounterfactualRealisedRepairBoundary
repairBoundary = Repair.canonicalCounterfactualRealisedRepairBoundary

tsfvBoundary : TSFV.TSFVMultiverseViabilityBoundary
tsfvBoundary = TSFV.canonicalTSFVMultiverseViabilityBoundary

arbitraryAlternativeStillNotCausalCounterfactual :
  Counterfactual.arbitraryAlternativeIsCausalCounterfactual counterfactualBoundary ≡ false
arbitraryAlternativeStillNotCausalCounterfactual = refl

selectedRepairWorldStillNotRobust :
  Repair.oneSuccessfulSelectedWorldProvesRobustRepair repairBoundary ≡ false
selectedRepairWorldStillNotRobust = refl

underidentificationStillNotNoEffect :
  Repair.underidentificationMeansNoCausalEffect repairBoundary ≡ false
underidentificationStillNotNoEffect = refl

parameterPointIsNotAutomaticallyRealisedUniverse :
  TSFV.parameterSpacePointIsAutomaticallyRealisedUniverse tsfvBoundary ≡ false
parameterPointIsNotAutomaticallyRealisedUniverse = refl

viableParameterRegionDoesNotProveMultiverse :
  TSFV.viableParameterRegionProvesMultiverse tsfvBoundary ≡ false
viableParameterRegionDoesNotProveMultiverse = refl

------------------------------------------------------------------------
-- Physics-specific reverse needs.
------------------------------------------------------------------------

data PhysicalCounterfactualNeed : Set where
  acquirePhysicalModel
  acquireBoundaryConditions
  acquireConservationOrConstraintCheck
  acquireCalibrationEvidence
  acquireExperimentalDiscriminator
  acquirePhysicalRealisationReceipt
  : PhysicalCounterfactualNeed

data PhysicalCounterfactualWork : Set where
  modelWork
  measurementWork
  experimentWork
  realisationWork
  : PhysicalCounterfactualWork

workForPhysicalNeed : PhysicalCounterfactualNeed → PhysicalCounterfactualWork
workForPhysicalNeed acquirePhysicalModel = modelWork
workForPhysicalNeed acquireBoundaryConditions = modelWork
workForPhysicalNeed acquireConservationOrConstraintCheck = modelWork
workForPhysicalNeed acquireCalibrationEvidence = measurementWork
workForPhysicalNeed acquireExperimentalDiscriminator = experimentWork
workForPhysicalNeed acquirePhysicalRealisationReceipt = realisationWork

------------------------------------------------------------------------
-- Physical law/experiment can prune or discriminate the admissible fibre.
------------------------------------------------------------------------

record PhysicallyExcludedWorld : Set where
  constructor physically-excluded-world
  field
    worldReference : String
    modelReference : String
    violatedConstraintReference : String
    exclusionReceipt : Set
    legalOrNormativeInadmissibilityClaimed : Bool
    legalOrNormativeInadmissibilityClaimedIsFalse :
      legalOrNormativeInadmissibilityClaimed ≡ false

record PhysicalDiscriminatorReceipt : Set where
  constructor physical-discriminator-receipt
  field
    leftWorldReference rightWorldReference : String
    observableReference : String
    experimentReference : String
    predictedDifferenceReceipt : Set
    measurementAuthorityReceipt : Set
    discriminatorCreatesLegalAuthority : Bool
    discriminatorCreatesLegalAuthorityIsFalse :
      discriminatorCreatesLegalAuthority ≡ false

open PhysicallyExcludedWorld public
open PhysicalDiscriminatorReceipt public

------------------------------------------------------------------------
-- Cross-domain no-promotion laws.
------------------------------------------------------------------------

data LegalAdmissibilityImpliesPhysicalCompatibility : Set where
data PhysicalCompatibilityImpliesLegalAdmissibility : Set where
data PhysicalExclusionCreatesLegalLiability : Set where
data PhysicalModelAdequacyCreatesPoliticalLegitimacy : Set where
data ExperimentCreatesRemedyAuthority : Set where
data LegalNormSelectsPhysicalReality : Set where

legalAdmissibilityDoesNotProvePhysicalCompatibility :
  LegalAdmissibilityImpliesPhysicalCompatibility → ⊥
legalAdmissibilityDoesNotProvePhysicalCompatibility ()

physicalCompatibilityDoesNotProveLegalAdmissibility :
  PhysicalCompatibilityImpliesLegalAdmissibility → ⊥
physicalCompatibilityDoesNotProveLegalAdmissibility ()

physicalExclusionDoesNotCreateLegalLiability :
  PhysicalExclusionCreatesLegalLiability → ⊥
physicalExclusionDoesNotCreateLegalLiability ()

physicalAdequacyDoesNotCreatePoliticalLegitimacy :
  PhysicalModelAdequacyCreatesPoliticalLegitimacy → ⊥
physicalAdequacyDoesNotCreatePoliticalLegitimacy ()

experimentDoesNotCreateRemedyAuthority : ExperimentCreatesRemedyAuthority → ⊥
experimentDoesNotCreateRemedyAuthority ()

legalNormDoesNotSelectPhysicalReality : LegalNormSelectsPhysicalReality → ⊥
legalNormDoesNotSelectPhysicalReality ()

record CounterfactualPhysicalRealisationBoundary : Set where
  constructor counterfactual-physical-realisation-boundary
  field
    physicalLawMayExcludeCandidateWorld : Bool
    physicalLawMayExcludeCandidateWorldIsTrue :
      physicalLawMayExcludeCandidateWorld ≡ true
    experimentMayDiscriminateCandidateWorlds : Bool
    experimentMayDiscriminateCandidateWorldsIsTrue :
      experimentMayDiscriminateCandidateWorlds ≡ true
    legalAdmissibilityEqualsPhysicalCompatibility : Bool
    legalAdmissibilityEqualsPhysicalCompatibilityIsFalse :
      legalAdmissibilityEqualsPhysicalCompatibility ≡ false
    theoryViabilityEqualsActualRealisation : Bool
    theoryViabilityEqualsActualRealisationIsFalse :
      theoryViabilityEqualsActualRealisation ≡ false
    physicalEvidenceCreatesLegalLiability : Bool
    physicalEvidenceCreatesLegalLiabilityIsFalse :
      physicalEvidenceCreatesLegalLiability ≡ false
    physicalEvidenceCreatesPoliticalAuthority : Bool
    physicalEvidenceCreatesPoliticalAuthorityIsFalse :
      physicalEvidenceCreatesPoliticalAuthority ≡ false

canonicalCounterfactualPhysicalRealisationBoundary :
  CounterfactualPhysicalRealisationBoundary
canonicalCounterfactualPhysicalRealisationBoundary =
  counterfactual-physical-realisation-boundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
