module DASHI.Biology.OpenEndedEvolutionHistoricalEvidenceCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List)
open import Data.Empty using (⊥)

import DASHI.Core.ExperimentalCoordinateDesignExact as Experiment
import DASHI.Biology.Evolution.EvolutionaryPopulationDynamics as Evolution
import DASHI.Biology.HeritableAgenticOrganisationEvolutionExact as Heritable
import DASHI.Biology.OpenEndedAgenticRepertoireEvolutionExact as OpenEnded
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Cognition.PNF.LearningAlgebra as Learning
import DASHI.Cognition.PNF.NeuralBottleneckResidualFutureSafetyExact as Neural
import DASHI.Biology.TraumaMemoryAttractorPortfolio as Trauma
import DASHI.Culture.AmalekAuthorityProjectionBoundary as Amalek
import Ontology.DNA.Supervoxel4Adic as DNA

------------------------------------------------------------------------
-- HISTORY-BEARING OPEN-ENDED EVOLUTION EVIDENCE
--
-- Abstract non-stabilisation is not yet an observation claim.  This owner adds
-- the missing history-bearing evidence carrier: an explicit experimental design,
-- measured capability novelty, provenance, optional molecular heredity, and
-- within-lifetime neural/memory/learning coordinates.  Trauma/path deformation
-- and Amalek/authority closure remain governance/cognitive coordinates rather
-- than genetic essences or historical inevitability theorems.
------------------------------------------------------------------------

record GenotypeDNARealisation
    (E : Evolution.EvolutionarySystem) : Set₁ where
  constructor genotype-dna-realisation
  field
    DNASequence : Set

    sequenceOf :
      Evolution.EvolutionarySystem.Genotype E → DNASequence

    baseSurface : DNASequence → List DNA.Base

    genotypeSequenceReference : String
    baseSurfaceReference : String
    molecularMeasurementReference : String

open GenotypeDNARealisation public

------------------------------------------------------------------------
-- Neural, thought/content, memory and learning remain distinct coordinates.
-- A shared current bottleneck code is already known to be weaker than future
-- neural equivalence, so no current cognitive projection is treated as a full
-- recoverable history.  Memory is carried in the repo-native append-only /
-- versioned fibre rather than replacing prior states.
------------------------------------------------------------------------

record CognitiveHistoryCoordinate : Set₁ where
  constructor cognitive-history-coordinate
  field
    ThoughtContent : Set

    neuralState : Neural.FineNeuralState
    thoughtContent : ThoughtContent
    versionedMemory : Memory.VersionedMemory
    learning : Learning.LearningReceipt

    learningStartsFromCurrentMemory :
      Learning.before learning ≡ Memory.current versionedMemory

    neuralReference : String
    thoughtReference : String
    memoryReference : String
    learningReference : String

open CognitiveHistoryCoordinate public

record TraumaHistoryCoordinate : Set₁ where
  constructor trauma-history-coordinate
  field
    branchHistory : List Trauma.BranchMemory
    learningResidues : List Trauma.BranchLearningResidue
    policyDeformation : Trauma.TraumaPolicyDeformation

    branchHistoryReference : String
    residueReference : String
    deformationReference : String

open TraumaHistoryCoordinate public

------------------------------------------------------------------------
-- One measured novelty episode.  The strong novelty witness is inherited from
-- OpenEndedAgenticRepertoireEvolutionExact, but this record additionally pays
-- the observation language and measurement/provenance coordinates.
------------------------------------------------------------------------

record ObservedCapabilityNoveltyEpisode
    {E : Evolution.EvolutionarySystem}
    {P : Heritable.AgenticArchitectureProjection E}
    (R : OpenEnded.AgenticRepertoireModel P) : Set₁ where
  constructor observed-capability-novelty-episode
  field
    earlierGeneration : Evolution.EvolutionarySystem.Generation E

    novelty :
      OpenEnded.LaterSelectedCapabilityNovelty R earlierGeneration

    World Control Value Dimension Result : Set

    experimentDesign :
      Experiment.ExperimentalCoordinateDesign World Control Value Dimension

    observedWorld : World
    result : Result

    CapabilityMeasured : Result → OpenEnded.Capability R → Set

    measuredNovelCapability :
      CapabilityMeasured result
        (OpenEnded.capability novelty)

    cognitiveHistory : CognitiveHistoryCoordinate
    traumaHistory : TraumaHistoryCoordinate

    chronologyReference : String
    lineageProvenanceReference : String
    measurementReference : String
    environmentReference : String
    observerReference : String

open ObservedCapabilityNoveltyEpisode public

------------------------------------------------------------------------
-- Optional molecular biological realization.  Simulated or non-DNA systems can
-- use ObservedCapabilityNoveltyEpisode directly; DNA is not made mandatory for
-- the abstract open-endedness concept.
------------------------------------------------------------------------

record MolecularBiologicalNoveltyEpisode
    {E : Evolution.EvolutionarySystem}
    {P : Heritable.AgenticArchitectureProjection E}
    {R : OpenEnded.AgenticRepertoireModel P}
    (episode : ObservedCapabilityNoveltyEpisode R) : Set₁ where
  constructor molecular-biological-novelty-episode
  field
    dnaRealisation : GenotypeDNARealisation E

    selectedDNA : DNASequence dnaRealisation

    selectedDNAMatchesGenotype :
      selectedDNA
      ≡ sequenceOf dnaRealisation
          (Evolution.EvolutionarySystem.genotypeOf E
            (Heritable.AgenticArchitectureSelectionReceipt.individual
              (OpenEnded.selectionReceipt (novelty episode))))

    dnaProvenanceReference : String

open MolecularBiologicalNoveltyEpisode public

------------------------------------------------------------------------
-- Finite traces are useful observations but cannot discharge the universal
-- non-stabilisation theorem by themselves.
------------------------------------------------------------------------

record FiniteInnovationEvidenceTrace
    {E : Evolution.EvolutionarySystem}
    {P : Heritable.AgenticArchitectureProjection E}
    (R : OpenEnded.AgenticRepertoireModel P) : Set₁ where
  constructor finite-innovation-evidence-trace
  field
    episodes : List (ObservedCapabilityNoveltyEpisode R)
    traceReference : String
    provenanceReference : String

open FiniteInnovationEvidenceTrace public

data FiniteTraceMeansUniversalOpenEndednessPermission : Set where

finiteTraceDoesNotByItselfProveUniversalOpenEndedness :
  FiniteTraceMeansUniversalOpenEndednessPermission → ⊥
finiteTraceDoesNotByItselfProveUniversalOpenEndedness ()

------------------------------------------------------------------------
-- A history-bearing capability non-stabilisation certificate requires one
-- measured novelty episode for every generation in the declared temporal
-- language.  From that stronger empirical carrier we recover the abstract
-- capability non-stabilisation theorem exactly.
------------------------------------------------------------------------

record HistoryBearingCapabilityNonStabilising
    {E : Evolution.EvolutionarySystem}
    {P : Heritable.AgenticArchitectureProjection E}
    (R : OpenEnded.AgenticRepertoireModel P) : Set₁ where
  constructor history-bearing-capability-non-stabilising
  field
    episodeAfter :
      (generation : Evolution.EvolutionarySystem.Generation E) →
      ObservedCapabilityNoveltyEpisode R

    episodeStartsAt :
      (generation : Evolution.EvolutionarySystem.Generation E) →
      earlierGeneration (episodeAfter generation) ≡ generation

    evidenceProgrammeReference : String

open HistoryBearingCapabilityNonStabilising public

historyToCapabilityNonStabilising :
  ∀ {E P R} →
  HistoryBearingCapabilityNonStabilising {E} {P} R →
  OpenEnded.CapabilityNonStabilising R
historyToCapabilityNonStabilising {R = R} H =
  OpenEnded.capability-non-stabilising
    (λ generation →
      subst
        (λ earlier → OpenEnded.LaterSelectedCapabilityNovelty R earlier)
        (episodeStartsAt H generation)
        (novelty (episodeAfter H generation)))
    (evidenceProgrammeReference H)

record HistoryBearingOpenEndedCertificate
    {E : Evolution.EvolutionarySystem}
    {P : Heritable.AgenticArchitectureProjection E}
    (R : OpenEnded.AgenticRepertoireModel P) : Set₁ where
  constructor history-bearing-open-ended-certificate
  field
    architectureNonStabilising : OpenEnded.ArchitecturallyNonStabilising R
    capabilityHistory : HistoryBearingCapabilityNonStabilising R

    architectureEvidenceReference : String
    historicalOpenEndednessReference : String

open HistoryBearingOpenEndedCertificate public

historyToOpenEndedInnovation :
  ∀ {E P R} →
  HistoryBearingOpenEndedCertificate {E} {P} R →
  OpenEnded.OpenEndedAgenticInnovation R
historyToOpenEndedInnovation H =
  OpenEnded.open-ended-agentic-innovation
    (architectureNonStabilising H)
    (historyToCapabilityNonStabilising (capabilityHistory H))
    (architectureEvidenceReference H)
    (historicalOpenEndednessReference H)

------------------------------------------------------------------------
-- Memory / trauma / authority-path boundaries.
------------------------------------------------------------------------

data PresentCapabilityMeansHistoryKnownPermission : Set where

data MemoryMeansGeneticInheritancePermission : Set where

data TraumaMeansDNAChangePermission : Set where

data NeuralStateMeansThoughtIdentityPermission : Set where

data LearningMeansOpenEndedEvolutionPermission : Set where

data CulturalNarrativeMeansGenotypePermission : Set where

data RememberedHarmMeansDominationPermission : Set where

presentCapabilityDoesNotRecoverHistory :
  PresentCapabilityMeansHistoryKnownPermission → ⊥
presentCapabilityDoesNotRecoverHistory ()

memoryDoesNotByItselfProveGeneticInheritance :
  MemoryMeansGeneticInheritancePermission → ⊥
memoryDoesNotByItselfProveGeneticInheritance ()

traumaDoesNotByItselfProveDNAChange :
  TraumaMeansDNAChangePermission → ⊥
traumaDoesNotByItselfProveDNAChange ()

neuralStateDoesNotDefinitionallyEqualThought :
  NeuralStateMeansThoughtIdentityPermission → ⊥
neuralStateDoesNotDefinitionallyEqualThought ()

learningDoesNotByItselfProveOpenEndedEvolution :
  LearningMeansOpenEndedEvolutionPermission → ⊥
learningDoesNotByItselfProveOpenEndedEvolution ()

culturalNarrativeDoesNotBecomeGenotype :
  CulturalNarrativeMeansGenotypePermission → ⊥
culturalNarrativeDoesNotBecomeGenotype ()

rememberedHarmDoesNotLicenseDomination :
  RememberedHarmMeansDominationPermission → ⊥
rememberedHarmDoesNotLicenseDomination ()

canonicalAmalekRememberedHarmDominationPromotionFalse :
  Amalek.rememberedHarmLicencesDominationPromotion
    Amalek.canonicalAmalekAuthorityProjectionBoundary
  ≡ false
canonicalAmalekRememberedHarmDominationPromotionFalse =
  Amalek.rememberedHarmLicencesDominationPromotionIsFalse
    Amalek.canonicalAmalekAuthorityProjectionBoundary

canonicalAmalekEssentialismPromotionFalse :
  Amalek.ethnicOrReligiousEssentialismPromotion
    Amalek.canonicalAmalekAuthorityProjectionBoundary
  ≡ false
canonicalAmalekEssentialismPromotionFalse =
  Amalek.ethnicOrReligiousEssentialismPromotionIsFalse
    Amalek.canonicalAmalekAuthorityProjectionBoundary

record HistoricalEvidenceCrossPollinationBoundary : Set where
  constructor historical-evidence-cross-pollination-boundary
  field
    openEndednessObservationNeedsMeasurementProgramme : Bool
    finiteNoveltyTraceIsUniversalOpenEndedness : Bool
    genotypeAndDNARequireExplicitRealisation : Bool
    neuralStateThoughtMemoryLearningRemainDistinct : Bool
    memoryIsVersionedRatherThanOverwritten : Bool
    traumaHistoryMayCarryLearningResidue : Bool
    traumaAutomaticallyMeansDNAChange : Bool
    culturalAuthorityPatternAutomaticallyMeansGenotype : Bool
    rememberedHarmLicencesDomination : Bool
    amalekMayEssentialiseHumanGroups : Bool

canonicalHistoricalEvidenceCrossPollinationBoundary :
  HistoricalEvidenceCrossPollinationBoundary
canonicalHistoricalEvidenceCrossPollinationBoundary =
  historical-evidence-cross-pollination-boundary
    true false true true true true false false false false
