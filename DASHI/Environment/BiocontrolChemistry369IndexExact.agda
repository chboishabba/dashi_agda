module DASHI.Environment.BiocontrolChemistry369IndexExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Chemistry.MechanismDiscriminationExact as ChemistryDiscrimination
import DASHI.Chemistry.OceanCarbonateSaltTemperatureStressBidiExact as AquaticChemistry
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ChemistryHyperfibreBridgeExact as Chemistry369
import DASHI.Environment.BiocontrolSIQuantityExact as SIQuantity

------------------------------------------------------------------------
-- BIOCONTROL -> ACTUAL-CHEMISTRY / 369-CHEMISTRY INDEX
--
-- This owner is deliberately thin.  It indexes the LES/biocontrol experiment
-- lane onto the repository's existing chemistry owners instead of creating a
-- parallel chemistry ontology.
--
-- The 369 chemistry hyperfibre is upstream structural machinery only:
-- atomic/valence -> molecular identity -> reaction enablement/conservation ->
-- kinetics/environment -> observed chemical state.  None of those arrows is an
-- automatic promotion.  Aquatic chemistry remains multi-coordinate and
-- experiment/mechanism discrimination remains source/protocol dependent.
------------------------------------------------------------------------

existing369ChemistryBoundary : Chemistry369.AtomicChemistryCrossPollinationBoundary
existing369ChemistryBoundary = Chemistry369.canonicalAtomicChemistryCrossPollinationBoundary

existingAquaticChemistryBoundary :
  AquaticChemistry.OceanCarbonateSaltTemperatureStressBoundary
existingAquaticChemistryBoundary =
  AquaticChemistry.canonicalOceanCarbonateSaltTemperatureStressBoundary

existingMechanismDiscriminationBoundary :
  ChemistryDiscrimination.DiscriminationBoundary
existingMechanismDiscriminationBoundary =
  ChemistryDiscrimination.canonicalDiscriminationBoundary

existingSIQuantityBoundary : SIQuantity.BiocontrolSIQuantityBoundary
existingSIQuantityBoundary = SIQuantity.canonicalBiocontrolSIQuantityBoundary

------------------------------------------------------------------------
-- Finite chemistry-specific obstruction.
--
-- A bulk nutrient mass-concentration class does not identify nutrient species.
-- The witness is synthetic DASHI mathematics.  It does not assert that these
-- two exact states have been observed at Springfield Lakes or any other site.
------------------------------------------------------------------------

data BulkNutrientMassClass : Set where
  sameBulkMassClass : BulkNutrientMassClass

data NitrogenSpeciesState : Set where
  nitrateDominant ammoniumDominant : NitrogenSpeciesState

data PHContext : Set where
  lowerPH higherPH : PHContext

record AquaticChemistryWorld : Set where
  constructor aquaticChemistryWorld
  field
    bulkNutrientMass : BulkNutrientMassClass
    nitrogenSpecies : NitrogenSpeciesState
    pHContext : PHContext

open AquaticChemistryWorld public

nitrateWorld : AquaticChemistryWorld
nitrateWorld = aquaticChemistryWorld sameBulkMassClass nitrateDominant higherPH

ammoniumWorld : AquaticChemistryWorld
ammoniumWorld = aquaticChemistryWorld sameBulkMassClass ammoniumDominant lowerPH

bulkNutrientObserver : AquaticChemistryWorld → BulkNutrientMassClass
bulkNutrientObserver = bulkNutrientMass

nitrogenSpeciesConsumer : AquaticChemistryWorld → NitrogenSpeciesState
nitrogenSpeciesConsumer = nitrogenSpecies

bulkNutrientCollision :
  bulkNutrientObserver nitrateWorld ≡ bulkNutrientObserver ammoniumWorld
bulkNutrientCollision = refl

speciesSeparation :
  nitrogenSpeciesConsumer nitrateWorld ≡ nitrogenSpeciesConsumer ammoniumWorld → ⊥
speciesSeparation ()

nutrientSpeciesNonFactorabilityWitness :
  NonFactor.NonFactorabilityWitness bulkNutrientObserver nitrogenSpeciesConsumer
nutrientSpeciesNonFactorabilityWitness =
  NonFactor.nonFactorabilityWitness nitrateWorld ammoniumWorld refl (λ ())

nutrientSpeciesDoesNotFactorThroughBulkMass :
  NonFactor.FactorsThrough bulkNutrientObserver nitrogenSpeciesConsumer → ⊥
nutrientSpeciesDoesNotFactorThroughBulkMass =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    nutrientSpeciesNonFactorabilityWitness

------------------------------------------------------------------------
-- Index contract.
------------------------------------------------------------------------

record BiocontrolChemistry369Index : Set₁ where
  constructor biocontrolChemistry369Index
  field
    chemistry369Boundary : Chemistry369.AtomicChemistryCrossPollinationBoundary
    aquaticChemistryBoundary : AquaticChemistry.OceanCarbonateSaltTemperatureStressBoundary
    mechanismDiscriminationBoundary : ChemistryDiscrimination.DiscriminationBoundary
    siQuantityBoundary : SIQuantity.BiocontrolSIQuantityBoundary
    indexReference : String

canonicalBiocontrolChemistry369Index : BiocontrolChemistry369Index
canonicalBiocontrolChemistry369Index = biocontrolChemistry369Index
  existing369ChemistryBoundary
  existingAquaticChemistryBoundary
  existingMechanismDiscriminationBoundary
  existingSIQuantityBoundary
  "biocontrol physical observations -> SI semantics -> analyte/speciation/environment chemistry -> mechanism discrimination; 369 supplies upstream atomic/molecular/reaction structure but does not replace downstream chemistry receipts"

record BiocontrolChemistry369Boundary : Set where
  constructor biocontrolChemistry369Boundary
  field
    actualChemistryIndexed : Bool
    actualChemistryIndexedIsTrue : actualChemistryIndexed ≡ true

    chemistry369Indexed : Bool
    chemistry369IndexedIsTrue : chemistry369Indexed ≡ true

    sameBulkNutrientMassDeterminesSpecies : Bool
    sameBulkNutrientMassDeterminesSpeciesIsFalse :
      sameBulkNutrientMassDeterminesSpecies ≡ false

    siDimensionDeterminesChemicalSpecies : Bool
    siDimensionDeterminesChemicalSpeciesIsFalse :
      siDimensionDeterminesChemicalSpecies ≡ false

    periodic369RecoveryDeterminesAquaticReactionState : Bool
    periodic369RecoveryDeterminesAquaticReactionStateIsFalse :
      periodic369RecoveryDeterminesAquaticReactionState ≡ false

    oneChemistryObservableProvesMechanism : Bool
    oneChemistryObservableProvesMechanismIsFalse :
      oneChemistryObservableProvesMechanism ≡ false

    pHNutrientOxygenHistoryRemainIndependentCoordinates : Bool
    pHNutrientOxygenHistoryRemainIndependentCoordinatesIsTrue :
      pHNutrientOxygenHistoryRemainIndependentCoordinates ≡ true

canonicalBiocontrolChemistry369Boundary : BiocontrolChemistry369Boundary
canonicalBiocontrolChemistry369Boundary = biocontrolChemistry369Boundary
  true refl
  true refl
  false refl
  false refl
  false refl
  false refl
  true refl
