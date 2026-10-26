module DASHI.Unified.BH4BiochemicalCrossScaleAdapter where

open import DASHI.Core.Prelude

import DASHI.Biology.BH4ReactionNetworkRunnerReceipt as Runner
import DASHI.Biology.Molecular.BH4MolecularStoichiometryExact as Stoich
import DASHI.Interop.BH4Atomic369RefinementExact as Refinement
import DASHI.Interop.PhysicsChemistryBiologyDNAUnificationDischarge as PhysicsChemistryBiologyDNAUnificationDischarge
import DASHI.Unified.CrossScaleMatterPhysics as CrossScaleMatterPhysics
import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- Bounded BH4 instance of the existing cross-scale matter scaffold.
------------------------------------------------------------------------

data BH4CrossScaleStage : Set where
  atomicInventoryStage : BH4CrossScaleStage
  molecularReactionStage : BH4CrossScaleStage
  biochemicalNetworkStage : BH4CrossScaleStage
  cellularStateStage : BH4CrossScaleStage

record BH4BiochemicalCrossScaleSurface : Set where
  constructor bh4-biochemical-cross-scale-surface
  field
    crossScaleParent : CrossScaleMatterPhysics.CrossScaleMatterPhysicsSurface
    biologyDischarge : PhysicsChemistryBiologyDNAUnificationDischarge.PhysicsChemistryBiologyDNAUnificationDischarge
    qdprStoichiometryPaid : Bool
    qdprRunnerReactionIdentityPaid : Bool
    atomic369RefinementPresent : Bool
    cellularStatePredictionPaid : Bool
    diseaseCausationPaid : Bool

open BH4BiochemicalCrossScaleSurface public

canonicalBH4BiochemicalCrossScaleSurface : BH4BiochemicalCrossScaleSurface
canonicalBH4BiochemicalCrossScaleSurface =
  bh4-biochemical-cross-scale-surface
    CrossScaleMatterPhysics.canonicalCrossScaleMatterPhysicsSurface
    PhysicsChemistryBiologyDNAUnificationDischarge.canonicalPhysicsChemistryBiologyDNAUnificationDischarge
    true
    true
    true
    false
    false

qdprCrossScaleStoichiometryPaid : qdprStoichiometryPaid canonicalBH4BiochemicalCrossScaleSurface ≡ true
qdprCrossScaleStoichiometryPaid = refl

qdprCrossScaleCellStateRemainsOpen : cellularStatePredictionPaid canonicalBH4BiochemicalCrossScaleSurface ≡ false
qdprCrossScaleCellStateRemainsOpen = refl

record BH4CrossScaleBoundary : Set where
  constructor bh4-cross-scale-boundary
  field
    adapterCreatesFirstPrinciplesAtomsToCellsDerivation : Bool
    adapterCreatesFirstPrinciplesAtomsToCellsDerivationIsFalse : adapterCreatesFirstPrinciplesAtomsToCellsDerivation ≡ false
    exactStoichiometryCreatesSolvedElectronicStructure : Bool
    exactStoichiometryCreatesSolvedElectronicStructureIsFalse : exactStoichiometryCreatesSolvedElectronicStructure ≡ false
    reactionNetworkCreatesCellStatePrediction : Bool
    reactionNetworkCreatesCellStatePredictionIsFalse : reactionNetworkCreatesCellStatePrediction ≡ false
    adapterCreatesDiseaseCausation : Bool
    adapterCreatesDiseaseCausationIsFalse : adapterCreatesDiseaseCausation ≡ false
    sharedCrossScaleParentIdentifiesScaleSemantics : Bool
    sharedCrossScaleParentIdentifiesScaleSemanticsIsFalse : sharedCrossScaleParentIdentifiesScaleSemantics ≡ false

open BH4CrossScaleBoundary public

canonicalBH4CrossScaleBoundary : BH4CrossScaleBoundary
canonicalBH4CrossScaleBoundary =
  bh4-cross-scale-boundary false refl false refl false refl false refl false refl

canonicalBH4BiochemicalCrossScaleReceipt : Receipt.GenericReceipt
canonicalBH4BiochemicalCrossScaleReceipt =
  Receipt.mkNonPromotingReceipt
    "BH4 biochemical cross-scale adapter"
    "DASHI.Unified.BH4BiochemicalCrossScaleAdapter"
    "QDPR finite atom inventory -> exact molecular stoichiometry -> reaction-network runner -> BH4 system-state payment -> existing CrossScaleMatterPhysics / PhysicsChemistryBiologyDNAUnificationDischarge parents"
    "instantiates the existing atoms-to-molecules-to-chemistry-to-cells scaffold with one exact bounded biochemical path while preserving the 369 refinement and external-provenance receipts"
    "no first-principles atoms-to-cells derivation, solved molecular Hamiltonian, measured cellular state, disease causation or full biology closure is promoted"
    "python3 scripts/check_bh4_chemistry_369_runner.py"
