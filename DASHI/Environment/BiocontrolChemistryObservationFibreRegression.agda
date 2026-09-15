module DASHI.Environment.BiocontrolChemistryObservationFibreRegression where

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Environment.BiocontrolChemistryObservationFibreExact as Chemistry

chemistryObservationFibre : Chemistry.ChemistryObservationFibre
chemistryObservationFibre = Chemistry.canonicalChemistryObservationFibre

bulkObserverCounterexample :
  MDL.ConsumerCounterexample Chemistry.chemistryObservationProblem Chemistry.bulkOnly
bulkObserverCounterexample = Chemistry.bulkOnlyCounterexample

bulkToChemistryRepair :
  MDL.LocalRefinementRepair
    Chemistry.chemistryObservationProblem
    Chemistry.bulkOnly
    Chemistry.analyteSpeciesContext
bulkToChemistryRepair = Chemistry.bulkToSpeciatedRepair

repairPaysEligibility :
  MDL.Eligible Chemistry.chemistryObservationProblem Chemistry.analyteSpeciesContext
repairPaysEligibility = Chemistry.repairProvidesSpeciatedEligibility

repairStaysLocal :
  MDL.sameNeighbourhood Chemistry.chemistryObserverNeighbourhood
    (MDL.address Chemistry.chemistryObserverNeighbourhood Chemistry.bulkOnly)
    (MDL.address Chemistry.chemistryObserverNeighbourhood Chemistry.analyteSpeciesContext)
repairStaysLocal = Chemistry.repairStaysInChemistryObserverFamily

boundary : Chemistry.BiocontrolChemistryObservationBoundary
boundary = Chemistry.canonicalBiocontrolChemistryObservationBoundary
