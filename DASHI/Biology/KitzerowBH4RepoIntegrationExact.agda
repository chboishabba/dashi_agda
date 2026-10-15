module DASHI.Biology.KitzerowBH4RepoIntegrationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.AllostaticBodyStateExact as Allostasis
import DASHI.Biology.Cell.CellStateAttractor as CellState
import DASHI.Biology.GenomeSensorimotorConnectomeBridge as GenomeBrain
import DASHI.Biology.NeurochemicalBrainCarrierBridge as Brain
import DASHI.Biology.NeurochemicalGenomicExpressionBridge as GeneExpression
import DASHI.Interop.PhysicsChemistryBiologyDNAUnificationDischarge as PCB
import DASHI.Promotion.ChemistryBiologyObligations as ChemBio
import DASHI.Promotion.NeurochemicalAuthorityBoundary as NeuroBoundary
import DASHI.Biology.KitzerowBH4CascadeExact as Cascade

------------------------------------------------------------------------
-- Thin adapter into existing repo owners.  The point is reuse: this tranche
-- does not define new allostasis, cell-state, connectome, neurochemical,
-- chemistry/biology, genomic-expression, or clinical-authority frameworks.
------------------------------------------------------------------------

record KitzerowBH4RepoIntegration : Set₁ where
  constructor kitzerowBH4RepoIntegration
  field
    cascade : Cascade.KitzerowBH4Cascade

    allostaticAnchor : Allostasis.AllostaticBodyState
    brainCarrierAnchor : Brain.NeurochemicalBrainCarrierBridge
    genomeConnectomeAnchor : GenomeBrain.GenomeSensorimotorConnectomeBridge
    genomicExpressionAnchor : GeneExpression.NeurochemicalGenomicExpressionBridge
    physicsChemistryBiologyDNAAnchor : PCB.PhysicsChemistryBiologyDNAUnificationDischarge

    chemistryBiologyObligationOwner : String
    neurochemicalAuthorityOwner : String
    cellStateOwner : String

    consumesBiologyCore : Bool
    consumesBiologyCoreIsTrue : consumesBiologyCore ≡ true
    consumesBrainNeurochemicalCore : Bool
    consumesBrainNeurochemicalCoreIsTrue : consumesBrainNeurochemicalCore ≡ true
    consumesChemistryBiologyInterop : Bool
    consumesChemistryBiologyInteropIsTrue : consumesChemistryBiologyInterop ≡ true

    promotesClinicalAuthority : Bool
    promotesClinicalAuthorityIsFalse : promotesClinicalAuthority ≡ false
    promotesBrainStateRecovery : Bool
    promotesBrainStateRecoveryIsFalse : promotesBrainStateRecovery ≡ false
    promotesGenomeToBehaviorClosure : Bool
    promotesGenomeToBehaviorClosureIsFalse : promotesGenomeToBehaviorClosure ≡ false

open KitzerowBH4RepoIntegration public

canonicalKitzerowBH4RepoIntegration : KitzerowBH4RepoIntegration
canonicalKitzerowBH4RepoIntegration =
  kitzerowBH4RepoIntegration
    Cascade.canonicalKitzerowBH4Cascade
    Allostasis.regulatedExtended
    Brain.canonicalNeurochemicalBrainCarrierBridge
    GenomeBrain.canonicalGenomeSensorimotorConnectomeBridge
    GeneExpression.canonicalNeurochemicalGenomicExpressionBridge
    PCB.canonicalPhysicsChemistryBiologyDNAUnificationDischarge
    "DASHI.Promotion.ChemistryBiologyObligations"
    "DASHI.Promotion.NeurochemicalAuthorityBoundary"
    "DASHI.Biology.Cell.CellStateAttractor"
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Explicit consumption witnesses keep the bridge tied to the existing
-- promotion boundaries instead of merely naming them in documentation.
------------------------------------------------------------------------

canonicalNeurochemicalBoundary : NeuroBoundary.NeurochemicalAuthorityBoundary
canonicalNeurochemicalBoundary = NeuroBoundary.canonicalNeurochemicalAuthorityBoundary

chemistryBiologyBoundaryReference : String
chemistryBiologyBoundaryReference = "ChemistryBiologyObligations: calibrated chemistry/biology authority remains required"

cellStateBoundaryReference : String
cellStateBoundaryReference = "CellStateAttractor: a molecular/regulatory perturbation is not the complete cell or brain state"
