module DASHI.Biology.Evolution.EvolutionaryGenomeMoveCoverageBridgeExact where

------------------------------------------------------------------------
-- Cross-pollination of the source's two differently quantified observations:
--
-- * all 406 pairwise fusions among 29 reconstructed ancestral linkage groups
--   are represented somewhere in sampled metazoan diversity;
-- * the much larger within-chromosome combinatorial potential remains far from
--   exhausted.
--
-- Source:
-- Darrin T. Schultz; Arno Blümel; Dalila Destanović; Fatih Sarigol;
-- Oleg Simakov (2026),
-- "Topological mixing and irreversibility in animal chromosome evolution",
-- Science Advances 12(34), eadz5561.
-- DOI: 10.1126/sciadv.adz5561
--
-- DASHI does not identify the tiny witness below with those 406 empirical
-- fusion classes.  It formalises the quantifier distinction they motivate:
-- every generator may be witnessed somewhere without every state being
-- reachable from every other state.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.GeneratorCoverageReachabilityExact as Coverage
import DASHI.Core.TrajectoryResidueExact as Path
import DASHI.Biology.Evolution.EvolutionaryGenomeTopologyIrreversibilityExact as Genome
import DASHI.Biology.Evolution.EvolutionaryGenomeTrajectoryResidueBridgeExact as Residue

------------------------------------------------------------------------
-- Labeled version of the schematic architecture transition vocabulary.
------------------------------------------------------------------------

data ArchitectureGenerator : Set where
  fusionGenerator dissociationGenerator : ArchitectureGenerator

data LabeledArchitectureStep :
  ArchitectureGenerator →
  Genome.GenomeArchitecture →
  Genome.GenomeArchitecture →
  Set where
  labeledFusion :
    LabeledArchitectureStep
      fusionGenerator
      Genome.ancestralSeparated
      Genome.fusedAndMixed
  labeledDissociation :
    LabeledArchitectureStep
      dissociationGenerator
      Genome.fusedAndMixed
      Genome.postMixDissociated

allSchematicGeneratorsWitnessed :
  Coverage.AllGeneratorsWitnessed LabeledArchitectureStep
allSchematicGeneratorsWitnessed fusionGenerator =
  Genome.ancestralSeparated , Genome.fusedAndMixed , labeledFusion
allSchematicGeneratorsWitnessed dissociationGenerator =
  Genome.fusedAndMixed , Genome.postMixDissociated , labeledDissociation

------------------------------------------------------------------------
-- The same persistent mixing residue survives the generator-erased labeled
-- transition system.
------------------------------------------------------------------------

labeledMixingResidueNeverErased :
  Path.NoResidueErasure
    (Coverage.ErasedStep LabeledArchitectureStep)
    Residue.mixingResidue
labeledMixingResidueNeverErased (fusionGenerator , labeledFusion) ()
labeledMixingResidueNeverErased (dissociationGenerator , labeledDissociation) refl = refl

postMixCannotReachAncestralUnderCoveredVocabulary :
  ¬ Path.Trace
      (Coverage.ErasedStep LabeledArchitectureStep)
      Genome.postMixDissociated
      Genome.ancestralSeparated
postMixCannotReachAncestralUnderCoveredVocabulary =
  Path.presentResidueBlocksTraceToAbsent
    labeledMixingResidueNeverErased
    refl
    refl

------------------------------------------------------------------------
-- Complete generator coverage therefore does not entail universal reachability
-- in this exact witness.
------------------------------------------------------------------------

completeGeneratorCoverageDoesNotEntailUniversalReachability :
  ¬ (Coverage.AllGeneratorsWitnessed LabeledArchitectureStep →
     Coverage.UniversallyReachable LabeledArchitectureStep)
completeGeneratorCoverageDoesNotEntailUniversalReachability =
  Coverage.coverageWithUnreachablePairRefutesUniversalEntailment
    allSchematicGeneratorsWitnessed
    postMixCannotReachAncestralUnderCoveredVocabulary

record GenomeMoveCoverageBridge : Set where
  constructor genomeMoveCoverageBridge
  field
    sourceAttribution : Genome.SourceAttribution
    sourceAttributionIsCanonical :
      sourceAttribution ≡ Genome.canonicalSourceAttribution

    allLocalGeneratorsHaveWitnesses :
      Coverage.AllGeneratorsWitnessed LabeledArchitectureStep

    universalReachabilityStillFails :
      ¬ Coverage.UniversallyReachable LabeledArchitectureStep

    sourceReportedAll406PairwiseFusionsSampled : Bool
    sourceReportedAll406PairwiseFusionsSampledIsTrue :
      sourceReportedAll406PairwiseFusionsSampled ≡ true

    sourceReportedCombinatorialSpaceFarFromExhausted : Bool
    sourceReportedCombinatorialSpaceFarFromExhaustedIsTrue :
      sourceReportedCombinatorialSpaceFarFromExhausted ≡ true

    tinyWitnessIsLiteralModelOf406FusionClasses : Bool
    tinyWitnessIsLiteralModelOf406FusionClassesIsFalse :
      tinyWitnessIsLiteralModelOf406FusionClasses ≡ false

open GenomeMoveCoverageBridge public

notUniversallyReachable :
  ¬ Coverage.UniversallyReachable LabeledArchitectureStep
notUniversallyReachable universal =
  postMixCannotReachAncestralUnderCoveredVocabulary
    (universal Genome.postMixDissociated Genome.ancestralSeparated)

canonicalGenomeMoveCoverageBridge : GenomeMoveCoverageBridge
canonicalGenomeMoveCoverageBridge =
  genomeMoveCoverageBridge
    Genome.canonicalSourceAttribution
    refl
    allSchematicGeneratorsWitnessed
    notUniversallyReachable
    true refl
    true refl
    false refl
