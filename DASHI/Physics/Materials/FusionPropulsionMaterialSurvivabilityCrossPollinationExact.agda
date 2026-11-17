module DASHI.Physics.Materials.FusionPropulsionMaterialSurvivabilityCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Culture.NASAFusionPlasmaSpacePropulsionBridgeExact as Fusion
import DASHI.Physics.Materials.RezaBurnResistantAlloyBidiExact as Reza
import DASHI.Physics.Materials.NickelBaseSuperalloyMechanismExact as Ni
import DASHI.Physics.Materials.FangDainingActiveMechanicalMetamaterialBidiExact as Fang
import DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact as Anti

------------------------------------------------------------------------
-- FUSION PROPULSION x MATERIAL SURVIVABILITY
--
-- This owner preserves a real cross-domain engineering intersection without
-- collapsing distinct propulsion environments.  Reza/Jacinto/Hardwick address
-- oxygen-rich chemical-rocket combustion.  NASA fusion-propulsion concepts use
-- magnetized plasma, lithium/metal propellant, magnetic nozzles, FRCs and HTS
-- coils.  Both create material-survivability consumers, but not the same one.
------------------------------------------------------------------------

data PropulsionMaterialEnvironment : Set where
  highPressureOxygenCombustion
  magnetizedFusionPlasma
  cryogenicSuperconductingCoil
  plasmaRadiationStandOff
  architectedMetamaterialEnvironment : PropulsionMaterialEnvironment

record FusionPropulsionMaterialIntersection : Set where
  constructor fusion-propulsion-material-intersection
  field
    environment : PropulsionMaterialEnvironment
    sourceObject : String
    materialQuestion : String
    crystalOrArchitectureScale : String
    exactSameObjectBridgePaid : Bool
    sourceReference : String

open FusionPropulsionMaterialIntersection public

rezaOxygenRichIntersection : FusionPropulsionMaterialIntersection
rezaOxygenRichIntersection = fusion-propulsion-material-intersection
  highPressureOxygenCombustion
  "Jacinto/Hardwick burn-resistant nickel-alloy family"
  "survive sustained combustion in high-pressure oxygen while retaining structural strength"
  "FCC gamma matrix; ordered L1_2 gamma-prime Ni3(Al,Ti); grain-boundary and oxide-scale state"
  true
  "US20030053926A1; US20040208777A1; NASA MSFC 2015 Oxygen-Rich Assessment of Mondaloy Alloy"

fusionDrivenRocketIntersection : FusionPropulsionMaterialIntersection
fusionDrivenRocketIntersection = fusion-propulsion-material-intersection
  magnetizedFusionPlasma
  "NASA Fusion Driven Rocket"
  "liner/propellant response under magnetically driven implosion, fusion heating, ionisation and magnetic-nozzle expansion"
  "metal-liner mesoscale/dynamic state; plasma-facing and thermal-survivability problem"
  true
  "NASA TechPort: The Fusion Driven Rocket, current project page 11570; earlier repo programme coordinate retained separately"

directFusionDriveIntersection : FusionPropulsionMaterialIntersection
directFusionDriveIntersection = fusion-propulsion-material-intersection
  cryogenicSuperconductingCoil
  "NASA Direct Fusion Drive / PFRC superconducting-coil subsystem"
  "HTS coil critical current, 20-30 K cooling, shielding, radiation damage and structural-mass tradeoff"
  "superconducting material state and coil architecture"
  true
  "NASA TechPort project 93785 plus Direct Fusion Drive project 93869/93994 manifestations"

fangArchitectedIntersection : FusionPropulsionMaterialIntersection
fangArchitectedIntersection = fusion-propulsion-material-intersection
  architectedMetamaterialEnvironment
  "Fang Daining active mechanical metamaterials"
  "architecture-derived mechanical response under thermal, chemical, light, electric, magnetic and pressure stimuli"
  "designed architecture / effective-property scale, not nominal alloy composition"
  true
  "DOI 10.1002/advs.202102662"

------------------------------------------------------------------------
-- Historical quantum-vacuum wording in a fusion/propulsion programme.
--
-- NASA TechPort's Direct Energy Conversion for Nuclear Propulsion at Low
-- Specific Mass project discusses aneutronic-fusion products, TWDEC and plasma
-- propulsion, and its anticipated-benefits text mentions a 'Quantum Vacuum
-- thruster'.  That is an official historical mention, not a thrust-validation
-- receipt and not a zero-point-energy extraction receipt.
------------------------------------------------------------------------

record QuantumVacuumProgrammeMention : Set where
  constructor quantum-vacuum-programme-mention
  field
    programme : String
    paidKernel : String
    demonstratedVacuumThrust : Bool
    demonstratedZeroPointExtraction : Bool
    sameObjectWithAmyMechanism : Bool
    sourceReference : String

open QuantumVacuumProgrammeMention public

nasaTWDECQuantumVacuumMention : QuantumVacuumProgrammeMention
nasaTWDECQuantumVacuumMention = quantum-vacuum-programme-mention
  "NASA JSC Direct Energy Conversion for Nuclear Propulsion at Low Specific Mass"
  "official NASA technology-planning text mentions Quantum Vacuum thruster as a possible future electric-propulsion partner alongside VASIMR-class systems"
  false
  false
  false
  "NASA TechPort project 12110"

------------------------------------------------------------------------
-- Reuse existing exact science owners.
------------------------------------------------------------------------

existingFusionDrivenRocketBridge : Fusion.fusionToPropulsionPromoted ≡ Fusion.fusionToPropulsionPromoted
existingFusionDrivenRocketBridge = refl

existingDirectFusionDriveBridge : Fusion.frcToPropulsionPromoted ≡ Fusion.frcToPropulsionPromoted
existingDirectFusionDriveBridge = refl

existingRezaAlloyBoundary : Reza.RezaAlloyBoundary
existingRezaAlloyBoundary = Reza.canonicalRezaAlloyBoundary

existingNickelBoundary : Ni.SuperalloyBoundary
existingNickelBoundary = Ni.canonicalSuperalloyBoundary

existingFangBoundary : Fang.FangMetamaterialBoundary
existingFangBoundary = Fang.canonicalFangMetamaterialBoundary

existingAntigravityBoundary : Anti.AntigravityPromotionBoundary
existingAntigravityBoundary = Anti.canonicalAntigravityPromotionBoundary

------------------------------------------------------------------------
-- Named firewalls.
------------------------------------------------------------------------

gammaPrimeIsCrystalScaleMechanism : Bool
gammaPrimeIsCrystalScaleMechanism = true

oxygenRichChemicalRocketIsNotFusionPropulsion : Bool
oxygenRichChemicalRocketIsNotFusionPropulsion = true

quantumVacuumMentionIsNotValidation : Bool
quantumVacuumMentionIsNotValidation = true

metamaterialArchitectureIsNotGammaPrimeCrystal : Bool
metamaterialArchitectureIsNotGammaPrimeCrystal = true

record FusionMaterialBoundary : Set where
  constructor fusion-material-boundary
  field
    sharedPropulsionWordImpliesSameMaterialEnvironment : Bool
    oxygenCompatibilityAutomaticallyTransfersToFusionPlasma : Bool
    gammaPrimeMicrostructureEqualsMechanicalMetamaterialArchitecture : Bool
    nasaQuantumVacuumMentionEstablishesOperationalVacuumThrust : Bool
    materialScienceMayGenerateCrossDomainAcquisitionTargets : Bool
    exactProgrammeOrSameObjectReceiptStillRequired : Bool

canonicalFusionMaterialBoundary : FusionMaterialBoundary
canonicalFusionMaterialBoundary = fusion-material-boundary
  false false false false true true
