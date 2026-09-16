module DASHI.Environment.BiocontrolChemistryActiveDiscriminatorRegression where

import DASHI.Core.ConsumerIndexedResidualRefinementExact as Consumer
import DASHI.Core.DiscriminatorSynthesisExact as Synthesis
import DASHI.Environment.BiocontrolChemistry369IndexExact as ChemistryIndex
import DASHI.Environment.BiocontrolChemistryActiveDiscriminatorExact as Search

bulkCollision :
  Consumer.ConsumerRelevantCollision
    ChemistryIndex.bulkNutrientObserver ChemistryIndex.nitrogenSpeciesConsumer
bulkCollision = Search.bulkNutrientSpeciesCollision

speciesBundleSeparates :
  Synthesis.BundleSeparates
    Search.speciesExperimentBundle
    ChemistryIndex.nitrateWorld
    ChemistryIndex.ammoniumWorld
speciesBundleSeparates = Search.speciesBundleSeparatesCollision

nitrateWorldRetained : Search.nitrateObservedFibre ChemistryIndex.nitrateWorld
nitrateWorldRetained = Search.nitrateWorldRemainsLive

boundary : Search.BiocontrolChemistryActiveDiscriminatorBoundary
boundary = Search.canonicalBiocontrolChemistryActiveDiscriminatorBoundary
