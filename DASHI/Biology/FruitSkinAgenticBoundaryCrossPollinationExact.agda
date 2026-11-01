module DASHI.Biology.FruitSkinAgenticBoundaryCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Biology.AgenticMaterialsControlCore as Agentic
import DASHI.Biology.AgenticMaterialsControlRegression as AgenticRegression
import DASHI.Biology.Cell.SelectiveMembraneBoundary as Membrane
import DASHI.Biology.Morphogenesis.RegenerativeRepairBoundary as Regeneration
import DASHI.Biology.FruitIntegrityAdversarialFibreExact as Fruit
import DASHI.Biology.FruitEmbodiedEnergyHistoryFibreExact as Energy

------------------------------------------------------------------------
-- FRUIT SKIN AS A PROTECTIVE BOUNDARY COMPETENCE FIBRE
--
-- This module does not identify fruit skin with a cell membrane.  It extracts
-- the shared structural role already represented by the cell owner:
--
--   oriented inside/outside boundary
--   + selective transport / permeability
--   + protection of an internal material state
--   + possible damage and resource-dependent repair.
--
-- The fruit skin is therefore more than a visible hash surface, while still
-- remaining distinct from the protected seeds, the fruit interior and the
-- whole plant.
------------------------------------------------------------------------

data FruitSkinState : Set where
  skinIntact skinBreached skinResealed : FruitSkinState

data BoundaryExposure : Set where
  restrictedExposure increasedExposure : BoundaryExposure

data ProtectedInterior : Set where
  interiorProtected interiorExposed : ProtectedInterior

skinExposure : FruitSkinState → BoundaryExposure
skinExposure skinIntact = restrictedExposure
skinExposure skinBreached = increasedExposure
skinExposure skinResealed = restrictedExposure

protectedInterior : FruitSkinState → ProtectedInterior
protectedInterior skinIntact = interiorProtected
protectedInterior skinBreached = interiorExposed
protectedInterior skinResealed = interiorProtected

skinSurface : FruitSkinState → Fruit.SurfaceIntegrity
skinSurface skinIntact = Fruit.apparentlyIntact
skinSurface skinBreached = Fruit.visiblyPartiallyEaten
skinSurface skinResealed = Fruit.apparentlyIntact

------------------------------------------------------------------------
-- Protective-boundary comparison with the cell membrane owner.
--
-- The comparison is typed as a role correspondence, not mechanism identity.
------------------------------------------------------------------------

record FruitSkinSelectiveBoundaryBridge
    (M : Membrane.SelectiveMembraneSystem) : Set₁ where
  open Membrane.SelectiveMembraneSystem M
  field
    fruitSkinMembrane : Membrane
    protectedSpecies : Species
    intactCellState : CellState
    skinMapsInsideToOutsideOrientation :
      MaintainsOrientation fruitSkinMembrane Membrane.inside Membrane.outside
    protectedSpeciesPermeabilityIsExplicit :
      PermeableTo fruitSkinMembrane protectedSpecies → Set
    reading : String

open FruitSkinSelectiveBoundaryBridge public

------------------------------------------------------------------------
-- Same present surface may hide different boundary histories.
------------------------------------------------------------------------

intactAndResealedHaveSameSurface :
  skinSurface skinIntact ≡ skinSurface skinResealed
intactAndResealedHaveSameSurface = refl

intactAndBreachedHaveDifferentExposure :
  skinExposure skinIntact ≡ skinExposure skinBreached → ⊥
intactAndBreachedHaveDifferentExposure ()

------------------------------------------------------------------------
-- Agentic-material cross-pollination.
--
-- We reuse the existing finite wound-repair material as the control-pattern
-- donor.  Fruit skin states are mapped into its target-relative repair fibre;
-- this does not assert that fruit peel has an independent mind or nervous
-- system.  Agency, when discussed, belongs only to a supplied closed-loop
-- material realisation satisfying AgenticMaterial's observation/action/defect
-- and corrective-feedback obligations.
------------------------------------------------------------------------

skinToTissueState : FruitSkinState → AgenticRegression.TissueState
skinToTissueState skinIntact = AgenticRegression.viable0
skinToTissueState skinBreached = AgenticRegression.damaged1
skinToTissueState skinResealed = AgenticRegression.viable0

skinRepairComparison :
  Agentic.closedLoopStep
    AgenticRegression.canonicalTissueMaterial
    (skinToTissueState skinBreached)
  ≡ skinToTissueState skinResealed
skinRepairComparison = refl

record FruitSkinAgenticRealisation : Set₁ where
  constructor fruit-skin-agentic-realisation
  field
    material : Agentic.AgenticMaterial
    encodeSkin : FruitSkinState → Agentic.State material
    intactIsTarget : encodeSkin skinIntact ≡ Agentic.target material
    breachedRepairsTowardTarget :
      Agentic.better material
        (Agentic.defect material
          (Agentic.closedLoopStep material (encodeSkin skinBreached)))
        (Agentic.defect material (encodeSkin skinBreached))
    energeticBookkeepingRetained : Agentic.OpenSystemBookkeeping
    energeticBookkeepingMatches :
      energeticBookkeepingRetained ≡ Agentic.thermodynamics material

open FruitSkinAgenticRealisation public

------------------------------------------------------------------------
-- Repair remains resource-dependent through the existing regeneration owner.
------------------------------------------------------------------------

record FruitSkinRegenerativeRepairAdapter
    (R : Regeneration.RegenerativeRepairSystem) : Set₁ where
  open Regeneration.RegenerativeRepairSystem R
  field
    encodeSkinTissue : FruitSkinState → TissueState
    intactMorphology : Morphology
    breachPerturbation : Perturbation
    repairEnvironment : Environment
    repairResource : Resource
    repairAction : RepairAction
    resourcesAvailableAfterBreach :
      ResourceAvailable repairResource
        (perturb breachPerturbation (encodeSkinTissue skinIntact))
    repairActionAdmissibleAfterBreach :
      ActionAdmissible repairAction
        (perturb breachPerturbation (encodeSkinTissue skinIntact))

open FruitSkinRegenerativeRepairAdapter public

------------------------------------------------------------------------
-- Embodied-energy protection overlay.
------------------------------------------------------------------------

record SkinProtectedInvestment : Set where
  constructor skin-protected-investment
  field
    skinState : FruitSkinState
    embodiedInvestment : Energy.EmbodiedEnergy
    interior : ProtectedInterior

open SkinProtectedInvestment public

intactSkinProtectsEmbodiedInvestment : SkinProtectedInvestment
intactSkinProtectsEmbodiedInvestment =
  skin-protected-investment
    skinIntact
    (Energy.joules 14)
    interiorProtected

breachedSkinExposesEmbodiedInvestment : SkinProtectedInvestment
breachedSkinExposesEmbodiedInvestment =
  skin-protected-investment
    skinBreached
    (Energy.joules 14)
    interiorExposed

sameInvestmentDifferentBoundaryProtection :
  embodiedInvestment intactSkinProtectsEmbodiedInvestment ≡
    embodiedInvestment breachedSkinExposesEmbodiedInvestment
sameInvestmentDifferentBoundaryProtection = refl

boundaryProtectionDiffersAtSameInvestment :
  interior intactSkinProtectsEmbodiedInvestment ≡
    interior breachedSkinExposesEmbodiedInvestment → ⊥
boundaryProtectionDiffersAtSameInvestment ()

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data FruitSkinIsCellMembranePermission : Set where

data ProtectiveBoundaryMeansAgencyPermission : Set where

data SkinDamageMeansSeedCompromisePermission : Set where

data ResealedSurfaceMeansOriginalHistoryPermission : Set where

data EmbodiedEnergyMeansProtectedAutomaticallyPermission : Set where

fruitSkinIsNotPromotedToCellMembraneIdentity :
  FruitSkinIsCellMembranePermission → ⊥
fruitSkinIsNotPromotedToCellMembraneIdentity ()

protectiveBoundaryDoesNotByItselfMeanAgency :
  ProtectiveBoundaryMeansAgencyPermission → ⊥
protectiveBoundaryDoesNotByItselfMeanAgency ()

skinDamageDoesNotByItselfMeanSeedCompromise :
  SkinDamageMeansSeedCompromisePermission → ⊥
skinDamageDoesNotByItselfMeanSeedCompromise ()

resealedSurfaceDoesNotRecoverOriginalHistory :
  ResealedSurfaceMeansOriginalHistoryPermission → ⊥
resealedSurfaceDoesNotRecoverOriginalHistory ()

embodiedEnergyDoesNotProtectItself :
  EmbodiedEnergyMeansProtectedAutomaticallyPermission → ⊥
embodiedEnergyDoesNotProtectItself ()

record FruitSkinAgenticBoundaryCrossPollinationBoundary : Set where
  constructor fruit-skin-agentic-boundary-cross-pollination-boundary
  field
    fruitSkinHasProtectiveBoundaryRole : Bool
    cellMembraneAndFruitSkinShareBoundaryStructureWithoutIdentity : Bool
    boundaryDamageMayExposeEmbodiedInvestment : Bool
    repairMayRestoreSurfaceWithoutErasingHistory : Bool
    protectiveBoundaryAloneImpliesAgency : Bool
    skinDamageAloneImpliesSeedCompromise : Bool

canonicalFruitSkinAgenticBoundaryCrossPollinationBoundary :
  FruitSkinAgenticBoundaryCrossPollinationBoundary
canonicalFruitSkinAgenticBoundaryCrossPollinationBoundary =
  fruit-skin-agentic-boundary-cross-pollination-boundary
    true true true true false false
