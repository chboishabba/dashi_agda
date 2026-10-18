module DASHI.Biology.Protein.ProteinConsumerFamilyBiocontrolCrossPollinationValidation where

open import DASHI.Core.Prelude

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Biology.Protein.ProteinConsumerProjectionAdequacyExact as Portfolio
import DASHI.Biology.Protein.ProteinConsumerFamilyRefinementKernelExact as Protein
import DASHI.Environment.BiocontrolChemistryObserverParetoExact as Biocontrol
import DASHI.Biology.Protein.ProteinConsumerFamilyBiocontrolCrossPollinationExact as Cross

proteinThermalMinimal :
  MDL.MinimalEligibleDescription
    (Protein.problemFor Portfolio.thermalResponseConsumer)
    Protein.identityPlusResidue
proteinThermalMinimal = Cross.proteinThermalSelectionDonor

biocontrolSpeciesMinimal :
  MDL.MinimalEligibleDescription
    Biocontrol.speciesProblem
    Biocontrol.speciesSensitive
biocontrolSpeciesMinimal = Cross.biocontrolSpeciesSelectionDonor

sharedArchitectureRetained : Bool
sharedArchitectureRetained = Cross.sharedAdequacyBeforeRankingArchitecture

biologyTransferBlocked : Bool
biologyTransferBlocked = Cross.proteinBiologyTransfersToBiocontrol

chemistryTransferBlocked : Bool
chemistryTransferBlocked = Cross.biocontrolChemistryTransfersToProtein

attributionTransferBlocked : Bool
attributionTransferBlocked = Cross.crossDomainSourceAttributionTransfers
