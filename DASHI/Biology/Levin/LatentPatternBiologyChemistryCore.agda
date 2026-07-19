module DASHI.Biology.Levin.LatentPatternBiologyChemistryCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.PatternMemoryCore as Memory
import DASHI.Biology.Levin.SyntheticLivingAgentBoundary as Synthetic
import DASHI.Biology.Levin.CellPhysicalOrganisationCore as CellPhysical
import DASHI.Biology.Levin.BioelectricChemistryWaveAdapter as Chemistry
import DASHI.Biology.Levin.EffortOutcomeAccounting as Accounting
import DASHI.Biology.Levin.FunctionalAgencyRatchet as Ratchet
import DASHI.Biology.Levin.NovelEmbodimentCompetence as Embodiment
import DASHI.Biology.Levin.LatentPatternInterfaceBoundary as Interface

------------------------------------------------------------------------
-- Umbrella for testable biology/chemistry and candidate latent-pattern
-- interpretations.  All stronger ontology remains optional and fail-closed.

record LatentPatternBiologyChemistryCore : Set where
  field
    patternMemoryLane        : Memory.PatternMemorySystem
    syntheticAgentBoundary   : Synthetic.SyntheticLivingAgentBoundary
    cellPhysicalLane         : CellPhysical.CellPhysicalOrganisationCore
    chemistryWaveLane        : Chemistry.BioelectricChemistryWaveAdapter
    effortBoundary           : Accounting.ResidualExplanationBoundary
    ratchetBoundary          : Ratchet.RatchetInterpretationBoundary
    latentInterfaceModel     : Interface.PatternInterfaceModel
    novelEmbodimentRequiresWitness : Bool
    inheritedPlasticityRemainsCandidate : Bool
    chemistryDoesNotFixSemantics : Bool
    latentOntologyNotPromoted : Bool
    clinicalAuthorityBlocked : Bool
    ethicalStatusNotDerivedFromMechanism : Bool
    interpretation : String

record ResearchProgrammeGate : Set where
  field
    quantifiedInputEffort      : Bool
    quantifiedOutcomeCompetence : Bool
    matchedPhysicalControls    : Bool
    historicalControls         : Bool
    mechanisticAlternatives    : Bool
    perturbationPredictions    : Bool
    crossSubstrateReplication  : Bool
    preregisteredExclusions    : Bool
    promotionAllowed           : Bool

canonicalResearchProgrammeGate : ResearchProgrammeGate
canonicalResearchProgrammeGate = record
  { quantifiedInputEffort = true
  ; quantifiedOutcomeCompetence = true
  ; matchedPhysicalControls = false
  ; historicalControls = false
  ; mechanisticAlternatives = true
  ; perturbationPredictions = false
  ; crossSubstrateReplication = false
  ; preregisteredExclusions = false
  ; promotionAllowed = false
  }

GeneticsAndEnvironmentAlwaysSufficient : Bool
GeneticsAndEnvironmentAlwaysSufficient = false

GeneticsAndEnvironmentNeverSufficient : Bool
GeneticsAndEnvironmentNeverSufficient = false

NovelMorphologyProvesNonphysicalMind : Bool
NovelMorphologyProvesNonphysicalMind = false

MathematicalStructureMayGuideHypothesisDesign : Bool
MathematicalStructureMayGuideHypothesisDesign = true
