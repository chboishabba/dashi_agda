module DASHI.Biology.Evolution.EvolutionaryGenomeTrajectoryResidueBridgeExact where

------------------------------------------------------------------------
-- Cross-pollination bridge:
-- Schultz et al. genome-topology witness -> generic DASHI trajectory residue.
--
-- Source attribution remains owned by
-- EvolutionaryGenomeTopologyIrreversibilityExact:
--
-- Darrin T. Schultz; Arno Blümel; Dalila Destanović; Fatih Sarigol;
-- Oleg Simakov (2026),
-- "Topological mixing and irreversibility in animal chromosome evolution",
-- Science Advances 12(34), eadz5561.
-- DOI: 10.1126/sciadv.adz5561
--
-- This bridge is DASHI mathematics over the schematic architecture witness.  It
-- does not assert that all biological chromosome rearrangements are globally
-- irreversible.  Its purpose is to expose the reusable theorem shape:
--
--   path deposits mixing residue
--       -> residue persists under allowed subsequent transitions
--       -> reverse trace to a residue-free state is impossible
--
-- and, independently,
--
--   same coarse chromosome-count observation
--       + different retained path residue
--       -> strict observer refinement / no residue descent through count alone.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.TrajectoryResidueExact as Path
import DASHI.Biology.Evolution.EvolutionaryGenomeTopologyIrreversibilityExact as Genome

------------------------------------------------------------------------
-- Collapse the source-specific two-valued MixingHistory carrier onto the
-- generic irreversible-residue flag.
------------------------------------------------------------------------

mixingResidue : Genome.GenomeArchitecture → Path.ResidueFlag
mixingResidue Genome.ancestralSeparated = Path.residueAbsent
mixingResidue Genome.fusedAndMixed = Path.residuePresent
mixingResidue Genome.postMixDissociated = Path.residuePresent

mixingHistoryAgreesWithResidueAtAncestor :
  Genome.mixingHistory Genome.ancestralSeparated ≡ Genome.noRecordedMixing
mixingHistoryAgreesWithResidueAtAncestor = refl

mixingHistoryAgreesWithResidueAfterFusion :
  Genome.mixingHistory Genome.fusedAndMixed ≡ Genome.recordedMixing
mixingHistoryAgreesWithResidueAfterFusion = refl

mixingHistoryAgreesWithResidueAfterDissociation :
  Genome.mixingHistory Genome.postMixDissociated ≡ Genome.recordedMixing
mixingHistoryAgreesWithResidueAfterDissociation = refl

------------------------------------------------------------------------
-- Persistence theorem.
--
-- Fusion creates the residue.  Once present, the only subsequent schematic
-- transition (dissociation after mixing) retains it.  The impossible premise
-- on fusion expresses that fusion begins in the residue-absent state.
------------------------------------------------------------------------

mixingResidueNeverErased :
  Path.NoResidueErasure Genome.ArchitectureStep mixingResidue
mixingResidueNeverErased Genome.fusionWithMixing ()
mixingResidueNeverErased Genome.dissociationAfterMixing refl = refl

------------------------------------------------------------------------
-- The canonical evolutionary lane is now a generic path-deposition witness.
------------------------------------------------------------------------

canonicalMixingTrace :
  Path.Trace Genome.ArchitectureStep
    Genome.ancestralSeparated Genome.postMixDissociated
canonicalMixingTrace =
  Path.traceStep Genome.fusionWithMixing
    (Path.traceStep Genome.dissociationAfterMixing Path.traceRefl)

canonicalMixingResidueDeposition :
  Path.ResidueDeposition Genome.ArchitectureStep mixingResidue
canonicalMixingResidueDeposition =
  Path.residueDeposition
    Genome.ancestralSeparated
    Genome.postMixDissociated
    canonicalMixingTrace
    refl
    refl

------------------------------------------------------------------------
-- Irreversibility follows from persistence, not merely by exhausting the two
-- constructors of the concrete transition relation.
------------------------------------------------------------------------

persistentMixingResidueBlocksReverseTrace :
  ¬ Path.Trace Genome.ArchitectureStep
      Genome.postMixDissociated Genome.ancestralSeparated
persistentMixingResidueBlocksReverseTrace =
  Path.presentResidueBlocksTraceToAbsent
    mixingResidueNeverErased
    refl
    refl

------------------------------------------------------------------------
-- Observer theorem: chromosome count recovers after the schematic
-- dissociation, while the path residue does not disappear.
------------------------------------------------------------------------

countPlusPathResidueStrictlyRefinesCount :
  Observer.StrictRefinement
    Genome.chromosomeCountShadow
    (Path.residueRefinedObserver Genome.chromosomeCountShadow mixingResidue)
countPlusPathResidueStrictlyRefinesCount =
  Path.coarseCollisionAcrossResidueGivesStrictRefinement
    Genome.chromosomeCountShadow
    mixingResidue
    Genome.ancestralSeparated
    Genome.postMixDissociated
    refl
    refl
    refl

mixingResidueDoesNotDescendThroughChromosomeCount :
  Path.ResidueDescendsThrough Genome.chromosomeCountShadow mixingResidue → ⊥
mixingResidueDoesNotDescendThroughChromosomeCount =
  Path.coarseCollisionAcrossResidueBlocksDescent
    refl
    refl
    refl

------------------------------------------------------------------------
-- Cross-pollination receipt.
------------------------------------------------------------------------

record GenomeTrajectoryResidueBridge : Set where
  constructor genomeTrajectoryResidueBridge
  field
    sourceAttribution : Genome.SourceAttribution
    sourceAttributionIsCanonical :
      sourceAttribution ≡ Genome.canonicalSourceAttribution

    deposition : Path.ResidueDeposition Genome.ArchitectureStep mixingResidue

    residuePersistence :
      Path.NoResidueErasure Genome.ArchitectureStep mixingResidue

    strictCountRefinement :
      Observer.StrictRefinement
        Genome.chromosomeCountShadow
        (Path.residueRefinedObserver Genome.chromosomeCountShadow mixingResidue)

    reverseTraceBlocked :
      ¬ Path.Trace Genome.ArchitectureStep
          Genome.postMixDissociated Genome.ancestralSeparated

    chromosomeCountDeterminesPathResidue : Bool
    chromosomeCountDeterminesPathResidueIsFalse :
      chromosomeCountDeterminesPathResidue ≡ false

    theoremIsSchematicDASHIExtension : Bool
    theoremIsSchematicDASHIExtensionIsTrue :
      theoremIsSchematicDASHIExtension ≡ true

open GenomeTrajectoryResidueBridge public

canonicalGenomeTrajectoryResidueBridge : GenomeTrajectoryResidueBridge
canonicalGenomeTrajectoryResidueBridge =
  genomeTrajectoryResidueBridge
    Genome.canonicalSourceAttribution
    refl
    canonicalMixingResidueDeposition
    mixingResidueNeverErased
    countPlusPathResidueStrictlyRefinesCount
    persistentMixingResidueBlocksReverseTrace
    false refl
    true refl
