module DASHI.Environment.BiocontrolAcquisitionParetoFrontierRegression where

open import DASHI.Core.Prelude

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Core.EvidenceAcquisitionSelectiveReopeningExact as Acquisition
import DASHI.Environment.BiocontrolAcquisitionParetoFrontierExact as Frontier

speciesParetoSelection :
  MDL.ParetoAdmissible
    Frontier.speciesAcquisitionCosts
    Frontier.speciesQualifiedPackage
speciesParetoSelection = Frontier.speciesAcquisitionPareto

contextParetoSelection :
  MDL.ParetoAdmissible
    Frontier.contextAcquisitionCosts
    Frontier.contextQualifiedPackage
contextParetoSelection = Frontier.contextAcquisitionPareto

provenanceIncompleteShortcutExcluded :
  MDL.Eligible Frontier.speciesAcquisitionProblem Frontier.metadataOnlyShortcut → ⊥
provenanceIncompleteShortcutExcluded = Frontier.metadataShortcutExcludedFromSpecies

speciesAcquisitionReopensRebound :
  Acquisition.SelectiveAcquisitionReopening
    Frontier.acquisitionFrontierDependencyGraph
    Frontier.speciesObservationArtifact
    Frontier.reboundConsumerArtifact
speciesAcquisitionReopensRebound = Frontier.speciesObservationReopensRebound

contextAcquisitionReopensClassification :
  Acquisition.SelectiveAcquisitionReopening
    Frontier.acquisitionFrontierDependencyGraph
    Frontier.contextObservationArtifact
    Frontier.calibratedClassificationArtifact
contextAcquisitionReopensClassification = Frontier.contextObservationReopensClassification

boundary : Frontier.BiocontrolAcquisitionParetoBoundary
boundary = Frontier.canonicalBiocontrolAcquisitionParetoBoundary
