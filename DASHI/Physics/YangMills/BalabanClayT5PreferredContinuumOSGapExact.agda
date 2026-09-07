{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5PreferredContinuumOSGapExact where

------------------------------------------------------------------------
-- T5 PHYSICAL CONTINUUM/OS/GAP: LEAST-PRIVILEGE SOURCE CUT
--
-- The historical PhysicalContinuumOSGapData asks for a reconstructed theory
-- plus the reconstruction function and an equality identifying the two.  It
-- likewise asks for a physical interlacing value plus the producing map and an
-- equality.  Those are redundant choices.
--
-- This preferred input keeps only the physical producers.  The reconstructed
-- theory and physical interlacing are defined from those producers, making both
-- historical same-object equalities refl.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4CombinedRGUVIterationExact as UV
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Physical
import DASHI.Physics.YangMills.BalabanClayT5OSGramTopologyExact as OS
import DASHI.Physics.YangMills.BalabanClayT5ConditionalClusteringCutsetExact as Clustering
import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMassTransportExact as Mass
import DASHI.Physics.YangMills.BalabanClayConcreteUVToMassGapDependencyExact as Dependency
import DASHI.Physics.YangMills.BalabanClayT5PhysicalContinuumOSGapBridgeExact as Old

record PreferredPhysicalContinuumOSGapInputs
    (State Bound Measure Observable Schwinger Scalar Hilbert Vector : Set) : Set₁ where
  field
    uvPackage : UV.Gate4UVCompletionPackage State Bound

    physicalGramData :
      Physical.PhysicalMeasureToOSGramData Measure Observable Scalar

    continuumClosure : Limit.FiniteToContinuumOSClosure Measure Schwinger

    physicalMeasureSequenceAgrees : ∀ cutoff →
      Physical.measureSequence
        (Physical.convergenceData physicalGramData) cutoff
      ≡ Limit.finiteMeasures continuumClosure cutoff

    physicalContinuumMeasureAgrees :
      Physical.continuumMeasure
        (Physical.convergenceData physicalGramData)
      ≡ Limit.continuumMeasure continuumClosure

    gramReflectionImpliesClosureReflection :
      OS.GramReflectionPositive
        (Physical.physicalMeasureTopologyControlsOSGram physicalGramData)
        (Limit.continuumMeasure continuumClosure) →
      Limit.ReflectionPositive continuumClosure
        (Limit.schwinger continuumClosure
          (Limit.continuumMeasure continuumClosure))

    clusteringCutset :
      Clustering.ConditionalClusteringAssembly Observable Scalar

    clusteringBoundImpliesClosureClustered :
      ((left right : Observable) →
        Clustering.LessEqual clusteringCutset
          (Clustering.covariance clusteringCutset left right)
          (Clustering.targetClusteringBound clusteringCutset left right)) →
      Limit.Clustered continuumClosure
        (Limit.schwinger continuumClosure
          (Limit.continuumMeasure continuumClosure))

    reconstructionFromOSAxioms :
      Dependency.ContinuumOSAxioms continuumClosure →
      Old.ReconstructedTransferTheory Hilbert Vector Scalar

    gapProducesPhysicalInterlacing :
      (theory : Old.ReconstructedTransferTheory Hilbert Vector Scalar) →
      Old.Positive theory (Old.spectralGap theory) →
      Mass.PhysicalMassInterlacing

open PreferredPhysicalContinuumOSGapInputs public

reconstructedTheory :
  ∀ {State Bound Measure Observable Schwinger Scalar Hilbert Vector}
    (inputs : PreferredPhysicalContinuumOSGapInputs
      State Bound Measure Observable Schwinger Scalar Hilbert Vector) →
  Old.ReconstructedTransferTheory Hilbert Vector Scalar
reconstructedTheory inputs =
  reconstructionFromOSAxioms inputs
    (Dependency.assembleContinuumOSAxioms (continuumClosure inputs))

physicalInterlacing :
  ∀ {State Bound Measure Observable Schwinger Scalar Hilbert Vector}
    (inputs : PreferredPhysicalContinuumOSGapInputs
      State Bound Measure Observable Schwinger Scalar Hilbert Vector) →
  Mass.PhysicalMassInterlacing
physicalInterlacing inputs =
  gapProducesPhysicalInterlacing inputs
    (reconstructedTheory inputs)
    (Old.spectralGapPositive (reconstructedTheory inputs))

asHistoricalPhysicalContinuumOSGapData :
  ∀ {State Bound Measure Observable Schwinger Scalar Hilbert Vector} →
  PreferredPhysicalContinuumOSGapInputs
    State Bound Measure Observable Schwinger Scalar Hilbert Vector →
  Old.PhysicalContinuumOSGapData
    State Bound Measure Observable Schwinger Scalar Hilbert Vector
asHistoricalPhysicalContinuumOSGapData inputs = record
  { Old.PhysicalContinuumOSGapData.uvPackage = uvPackage inputs
  ; Old.PhysicalContinuumOSGapData.physicalGramData = physicalGramData inputs
  ; Old.PhysicalContinuumOSGapData.continuumClosure = continuumClosure inputs
  ; Old.PhysicalContinuumOSGapData.physicalMeasureSequenceAgrees =
      physicalMeasureSequenceAgrees inputs
  ; Old.PhysicalContinuumOSGapData.physicalContinuumMeasureAgrees =
      physicalContinuumMeasureAgrees inputs
  ; Old.PhysicalContinuumOSGapData.gramReflectionImpliesClosureReflection =
      gramReflectionImpliesClosureReflection inputs
  ; Old.PhysicalContinuumOSGapData.clusteringCutset = clusteringCutset inputs
  ; Old.PhysicalContinuumOSGapData.clusteringBoundImpliesClosureClustered =
      clusteringBoundImpliesClosureClustered inputs
  ; Old.PhysicalContinuumOSGapData.reconstructedTheory =
      reconstructedTheory inputs
  ; Old.PhysicalContinuumOSGapData.reconstructionFromOSAxioms =
      reconstructionFromOSAxioms inputs
  ; Old.PhysicalContinuumOSGapData.reconstructionAgrees = refl
  ; Old.PhysicalContinuumOSGapData.physicalInterlacing =
      physicalInterlacing inputs
  ; Old.PhysicalContinuumOSGapData.gapProducesPhysicalInterlacing =
      gapProducesPhysicalInterlacing inputs
  ; Old.PhysicalContinuumOSGapData.interlacingAgrees = refl
  }

preferredPhysicalContinuumOSGapCompilerLevel : ProofLevel
preferredPhysicalContinuumOSGapCompilerLevel = machineChecked

literalPhysicalUVToContinuumMeasureInputsLevel : ProofLevel
literalPhysicalUVToContinuumMeasureInputsLevel = conditional

literalPhysicalOSReconstructionInputsLevel : ProofLevel
literalPhysicalOSReconstructionInputsLevel = conditional

literalPhysicalGapToInterlacingInputsLevel : ProofLevel
literalPhysicalGapToInterlacingInputsLevel = conditional
