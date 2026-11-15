module DASHI.Physics.Thermodynamics.MagnetocaloricConsumerAtlasExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Units.MagnetocaloricSIConsumerExact as SI
import DASHI.Physics.Electromagnetism.MagnetocaloricFieldConsumerExact as EM
import DASHI.Physics.CondensedMatter.MagnetocaloricCrystalQuantumConsumerExact as CM
import DASHI.Physics.Chemistry.MagnetocaloricAtomicChemistryConsumerExact as Chem
import DASHI.Physics.Quantum.MagnetocaloricQuantumStatMechConsumerExact as Quantum
import DASHI.Physics.Thermodynamics.MagnetocaloricContinuumConsumerExact as Fluid
import DASHI.Physics.Thermodynamics.MagnetocaloricMagnetostructuralConsumerExact as Mech
import DASHI.Physics.Thermodynamics.MagnothermAttributedEvidenceExact as Evidence
import DASHI.Physics.Thermodynamics.MagnetocaloricFamilyEvidenceExact as Family
import DASHI.Physics.Thermodynamics.MagnothermPolarisEvidenceExact as Polaris
import DASHI.Physics.Thermodynamics.MagnetocaloricEvidenceMaxCutExact as MaxCut

------------------------------------------------------------------------
-- Reachability/status atlas for the magnetocaloric vertical slice.
------------------------------------------------------------------------

data ReuseRole : Set where
  directPhysicalConsumer : ReuseRole
  structuralPrecedentOnly : ReuseRole
  explicitlyNotAConsumer : ReuseRole

data ConsumerDecision : Set where
  populated : ConsumerDecision
  coveredByExistingOwner : ConsumerDecision
  rejectedAsUnsoundCoupling : ConsumerDecision

record MagnetocaloricConsumerAtlas : Set where
  constructor magnetocaloric-consumer-atlas
  field
    siMetrologyPopulated : Bool
    electromagnetismPopulated : Bool
    condensedMatterPopulated : Bool
    atomicChemistryPopulated : Bool
    quantumStatMechPopulated : Bool
    continuumTransportPopulated : Bool
    magnetostructuralPopulated : Bool
    protectionChemistryPopulated : Bool
    attributedEvidencePopulated : Bool
    familyEvidencePopulated : Bool
    polarisDeviceEvidencePopulated : Bool
    empiricalMaxCutAtlasPopulated : Bool

    navierStokesRole : ReuseRole
    yangMillsRole : ReuseRole

    rotationalWorkDecision : ConsumerDecision
    heatExchangerDecision : ConsumerDecision
    genericControllerDecision : ConsumerDecision

canonicalMagnetocaloricConsumerAtlas : MagnetocaloricConsumerAtlas
canonicalMagnetocaloricConsumerAtlas =
  magnetocaloric-consumer-atlas
    true true true true true true true true true true true true
    structuralPrecedentOnly
    structuralPrecedentOnly
    coveredByExistingOwner
    coveredByExistingOwner
    rejectedAsUnsoundCoupling

record MagnetocaloricCrossDomainPromotionBoundary : Set where
  constructor magnetocaloric-cross-domain-promotion-boundary
  field
    siTypingIsNotCalibration : Bool
    u1FieldSocketIsNotMaterialLaw : Bool
    crystalSymmetryIsNotCaloricMagnitude : Bool
    atomicStructureIsNotBulkResponse : Bool
    protectionChemistryDoesNotProveLifetime : Bool
    quantumHamiltonianIsNotBulkThermodynamics : Bool
    continuumInterfaceIsNotClayRegularity : Bool
    elasticityDoesNotSupplyMagnetostriction : Bool
    nonAbelianYMIsNotApplicationMagnetism : Bool
    biologyControlCoreIsNotImportedAsEngineeringController : Bool
    citationDoesNotImportScientificAuthority : Bool
    vendorClaimDoesNotPaySameDeviceCalibration : Bool
    plannedExperimentDoesNotPayObservedLifetime : Bool
    familyCrystalEvidenceDoesNotIdentifyExactMaterial : Bool
    familyThermalTransportDoesNotSupplyDeviceHeatTransfer : Bool
    phenomenologicalMagnetoelasticModelDoesNotValidateMicroscopicHamiltonian : Bool
    polarisPlatformPerformanceDoesNotPromoteToLaFeSiMaterialPerformance : Bool
    polarisHydraulicsDoesNotCloseLaFeSiHydraulicClosure : Bool
    polarisDeploymentDoesNotProveLaFeSiLifetime : Bool

canonicalMagnetocaloricCrossDomainPromotionBoundary :
  MagnetocaloricCrossDomainPromotionBoundary
canonicalMagnetocaloricCrossDomainPromotionBoundary =
  magnetocaloric-cross-domain-promotion-boundary
    true true true true true true true true true true true true true true true true true true true

navierStokesIsStructuralOnly :
  MagnetocaloricConsumerAtlas.navierStokesRole canonicalMagnetocaloricConsumerAtlas
  ≡ structuralPrecedentOnly
navierStokesIsStructuralOnly = refl

yangMillsIsStructuralOnly :
  MagnetocaloricConsumerAtlas.yangMillsRole canonicalMagnetocaloricConsumerAtlas
  ≡ structuralPrecedentOnly
yangMillsIsStructuralOnly = refl
