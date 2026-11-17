module DASHI.Environment.BiocontrolChemistryObserverParetoRegression where

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Environment.BiocontrolChemistry369IndexExact as ChemistryIndex
import DASHI.Environment.BiocontrolChemistryObserverParetoExact as Pareto

speciesCollisionWitness :
  NonFactor.NonFactorabilityWitness
    ChemistryIndex.bulkNutrientObserver
    ChemistryIndex.nitrogenSpeciesConsumer
speciesCollisionWitness = Pareto.speciesCollisionWitness

bulkExcludedForSpecies :
  MDL.Eligible Pareto.speciesProblem Pareto.bulkOnly → ⊥
bulkExcludedForSpecies = Pareto.bulkExcludedFromSpeciesEligibility

speciesSelectedMinimal :
  MDL.MinimalEligibleDescription Pareto.speciesProblem Pareto.speciesSensitive
speciesSelectedMinimal = Pareto.speciesMinimalEligible

speciesSelectedPareto :
  MDL.ParetoAdmissible Pareto.speciesCostHyperfabric Pareto.speciesSensitive
speciesSelectedPareto = Pareto.speciesParetoAdmissible

speciesToContextualRepair :
  MDL.LocalRefinementRepair
    Pareto.contextualProblem Pareto.speciesSensitive Pareto.contextualChemistry
speciesToContextualRepair = Pareto.speciesToContextualRepair

speciesExcludedForContextualConsumer :
  MDL.Eligible Pareto.contextualProblem Pareto.speciesSensitive → ⊥
speciesExcludedForContextualConsumer = Pareto.speciesExcludedFromContextualEligibility

contextualSelectedMinimal :
  MDL.MinimalEligibleDescription
    Pareto.contextualProblem Pareto.contextualChemistry
contextualSelectedMinimal = Pareto.contextualMinimalEligible

contextualSelectedPareto :
  MDL.ParetoAdmissible
    Pareto.contextualCostHyperfabric Pareto.contextualChemistry
contextualSelectedPareto = Pareto.contextualParetoAdmissible

bulkRepairStaysLocal :
  MDL.sameNeighbourhood Pareto.speciesNeighbourhood
    (MDL.address Pareto.speciesNeighbourhood Pareto.bulkOnly)
    (MDL.address Pareto.speciesNeighbourhood Pareto.speciesSensitive)
bulkRepairStaysLocal = Pareto.bulkRepairStaysLocal

contextualRepairStaysLocal :
  MDL.sameNeighbourhood Pareto.contextualNeighbourhood
    (MDL.address Pareto.contextualNeighbourhood Pareto.speciesSensitive)
    (MDL.address Pareto.contextualNeighbourhood Pareto.contextualChemistry)
contextualRepairStaysLocal = Pareto.contextualRepairStaysLocal

boundary : Pareto.BiocontrolChemistryObserverParetoBoundary
boundary = Pareto.canonicalBiocontrolChemistryObserverParetoBoundary
