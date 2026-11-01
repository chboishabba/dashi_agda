{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5SelectedContinuumOSGapBridgeExact where

------------------------------------------------------------------------
-- SELECTED CONTINUUM OS/GAP BRIDGE
--
-- Preferred replacement for the legacy gap bridge.  It consumes only the
-- selected continuum OS carrier and its actual axiom bundle; no total limit
-- operator or arbitrary-sequence convergence theorem is required.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (zero)
open import Data.Rational using (_≤_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4CombinedRGUVIterationExact as UV
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Physical
import DASHI.Physics.YangMills.BalabanClayT5OSGramTopologyExact as OS
import DASHI.Physics.YangMills.BalabanClayT5ConditionalClusteringCutsetExact as Clustering
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMassTransportExact as Mass
import DASHI.Physics.YangMills.BalabanClayT5PhysicalContinuumOSGapBridgeExact as LegacyGap
import DASHI.Physics.YangMills.BalabanClayT5SelectedContinuumOSExact as Selected

record SelectedPhysicalContinuumOSGapInputs
    (State Bound Measure Observable Schwinger Scalar Hilbert Vector : Set) : Set₁ where
  field
    uvPackage : UV.Gate4UVCompletionPackage State Bound

    physicalGramData :
      Physical.PhysicalMeasureToOSGramData Measure Observable Scalar

    continuumClosure : Selected.SelectedFiniteToContinuumOS Measure Schwinger

    physicalMeasureSequenceAgrees : ∀ cutoff →
      Physical.measureSequence
        (Physical.convergenceData physicalGramData) cutoff
      ≡ Selected.finiteMeasures continuumClosure cutoff

    physicalContinuumMeasureAgrees :
      Physical.continuumMeasure
        (Physical.convergenceData physicalGramData)
      ≡ Selected.continuumMeasure continuumClosure

    gramReflectionImpliesSelectedReflection :
      OS.GramReflectionPositive
        (Physical.physicalMeasureTopologyControlsOSGram physicalGramData)
        (Selected.continuumMeasure continuumClosure) →
      Selected.ReflectionPositive continuumClosure
        (Selected.schwinger continuumClosure
          (Selected.continuumMeasure continuumClosure))

    clusteringCutset :
      Clustering.ConditionalClusteringAssembly Observable Scalar

    clusteringBoundImpliesSelectedClustered :
      ((left right : Observable) →
        Clustering.LessEqual clusteringCutset
          (Clustering.covariance clusteringCutset left right)
          (Clustering.targetClusteringBound clusteringCutset left right)) →
      Selected.Clustered continuumClosure
        (Selected.schwinger continuumClosure
          (Selected.continuumMeasure continuumClosure))

    reconstructionFromSelectedOSAxioms :
      Selected.SelectedContinuumOSAxioms continuumClosure →
      LegacyGap.ReconstructedTransferTheory Hilbert Vector Scalar

    gapProducesPhysicalInterlacing :
      (theory : LegacyGap.ReconstructedTransferTheory Hilbert Vector Scalar) →
      LegacyGap.Positive theory (LegacyGap.spectralGap theory) →
      Mass.PhysicalMassInterlacing

open SelectedPhysicalContinuumOSGapInputs public

selectedPhysicalGramReflectionPositiveAtClosure :
  ∀ {State Bound Measure Observable Schwinger Scalar Hilbert Vector}
    (inputs : SelectedPhysicalContinuumOSGapInputs
      State Bound Measure Observable Schwinger Scalar Hilbert Vector) →
  OS.GramReflectionPositive
    (Physical.physicalMeasureTopologyControlsOSGram
      (physicalGramData inputs))
    (Selected.continuumMeasure (continuumClosure inputs))
selectedPhysicalGramReflectionPositiveAtClosure inputs =
  subst
    (OS.GramReflectionPositive
      (Physical.physicalMeasureTopologyControlsOSGram
        (physicalGramData inputs)))
    (physicalContinuumMeasureAgrees inputs)
    (Physical.physicalContinuumReflectionPositive
      (physicalGramData inputs))

selectedContinuumReflectionPositive :
  ∀ {State Bound Measure Observable Schwinger Scalar Hilbert Vector}
    (inputs : SelectedPhysicalContinuumOSGapInputs
      State Bound Measure Observable Schwinger Scalar Hilbert Vector) →
  Selected.ReflectionPositive (continuumClosure inputs)
    (Selected.schwinger (continuumClosure inputs)
      (Selected.continuumMeasure (continuumClosure inputs)))
selectedContinuumReflectionPositive inputs =
  gramReflectionImpliesSelectedReflection inputs
    (selectedPhysicalGramReflectionPositiveAtClosure inputs)

selectedContinuumClustered :
  ∀ {State Bound Measure Observable Schwinger Scalar Hilbert Vector}
    (inputs : SelectedPhysicalContinuumOSGapInputs
      State Bound Measure Observable Schwinger Scalar Hilbert Vector) →
  Selected.Clustered (continuumClosure inputs)
    (Selected.schwinger (continuumClosure inputs)
      (Selected.continuumMeasure (continuumClosure inputs)))
selectedContinuumClustered inputs =
  clusteringBoundImpliesSelectedClustered inputs
    (Clustering.conditionalUniformClustering (clusteringCutset inputs))

selectedReconstructedTheory :
  ∀ {State Bound Measure Observable Schwinger Scalar Hilbert Vector}
    (inputs : SelectedPhysicalContinuumOSGapInputs
      State Bound Measure Observable Schwinger Scalar Hilbert Vector) →
  LegacyGap.ReconstructedTransferTheory Hilbert Vector Scalar
selectedReconstructedTheory inputs =
  reconstructionFromSelectedOSAxioms inputs
    (Selected.assembleSelectedContinuumOSAxioms (continuumClosure inputs))

selectedPhysicalInterlacing :
  ∀ {State Bound Measure Observable Schwinger Scalar Hilbert Vector}
    (inputs : SelectedPhysicalContinuumOSGapInputs
      State Bound Measure Observable Schwinger Scalar Hilbert Vector) →
  Mass.PhysicalMassInterlacing
selectedPhysicalInterlacing inputs =
  gapProducesPhysicalInterlacing inputs
    (selectedReconstructedTheory inputs)
    (LegacyGap.spectralGapPositive (selectedReconstructedTheory inputs))

selectedPhysicalMassTransport :
  ∀ {State Bound Measure Observable Schwinger Scalar Hilbert Vector}
    (inputs : SelectedPhysicalContinuumOSGapInputs
      State Bound Measure Observable Schwinger Scalar Hilbert Vector) →
  Mass.survivingMass (selectedPhysicalInterlacing inputs)
  ≤ Mass.physicalGap (selectedPhysicalInterlacing inputs) zero
selectedPhysicalMassTransport inputs =
  Mass.positivePhysicalMassSurvives (selectedPhysicalInterlacing inputs)

selectedContinuumOSGapCompilerLevel : ProofLevel
selectedContinuumOSGapCompilerLevel = machineChecked

selectedPhysicalMeasurePresentationAgreementLevel : ProofLevel
selectedPhysicalMeasurePresentationAgreementLevel = conditional

selectedGramToSchwingerReflectionMeaningLevel : ProofLevel
selectedGramToSchwingerReflectionMeaningLevel = conditional

selectedClusteringToOS4MeaningLevel : ProofLevel
selectedClusteringToOS4MeaningLevel = conditional

selectedOSReconstructionAuthorityLevel : ProofLevel
selectedOSReconstructionAuthorityLevel = standardImported

selectedGapToPhysicalInterlacingLevel : ProofLevel
selectedGapToPhysicalInterlacingLevel = conditional
