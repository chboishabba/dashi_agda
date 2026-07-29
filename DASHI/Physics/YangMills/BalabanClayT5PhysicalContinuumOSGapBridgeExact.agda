module DASHI.Physics.YangMills.BalabanClayT5PhysicalContinuumOSGapBridgeExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (zero)
open import Data.Rational using (_≤_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4CombinedRGUVIterationExact as UV
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Physical
import DASHI.Physics.YangMills.BalabanClayT5OSGramTopologyExact as OS
import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMassTransportExact as Mass
import DASHI.Physics.YangMills.BalabanClayConcreteUVToMassGapDependencyExact as Existing

------------------------------------------------------------------------
-- Primary provenance.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions",
-- Communications in Mathematical Physics 31 (1973), 83--112.
-- DOI: 10.1007/BF01645738.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions II",
-- Communications in Mathematical Physics 42 (1975), 281--305.
-- DOI: 10.1007/BF01608978.
--
-- P. Menotti and A. Pelissetto,
-- "General Proof of Osterwalder-Schrader Positivity for the Wilson Action",
-- Communications in Mathematical Physics 113 (1987), 369--373.
-- DOI: 10.1007/BF01221251.
--
-- Secondary locator only, not theorem authority:
-- Lluis Eriksson, "Exponential Clustering and Mass Gap for Four-Dimensional
-- SU(N) Lattice Yang--Mills Theory Via Balaban's Renormalization Group and
-- Multiscale Correlator Decoupling -- a Conditional Clustering Theorem --",
-- ai.viXra:2602.0088v3, no DOI recorded. Version 3 explicitly leaves H-KP,
-- H-LOC, H-Rbeta, H-P0', per-scale decoupling and OS1 conditional.
------------------------------------------------------------------------

record ReconstructedTransferTheory
    (Hilbert Vector Scalar : Set) : Set₁ where
  field
    hilbertSpace : Hilbert
    vacuum : Vector
    hamiltonian : Vector → Vector
    energy : Vector → Scalar
    spectralGap : Scalar
    Positive : Scalar → Set
    spectralGapPositive : Positive spectralGap

open ReconstructedTransferTheory public

record PhysicalContinuumOSGapData
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

    reconstructedTheory : ReconstructedTransferTheory Hilbert Vector Scalar

    reconstructionFromOSAxioms :
      Existing.ContinuumOSAxioms continuumClosure →
      ReconstructedTransferTheory Hilbert Vector Scalar

    reconstructionAgrees :
      reconstructionFromOSAxioms
        (Existing.assembleContinuumOSAxioms continuumClosure)
      ≡ reconstructedTheory

    physicalInterlacing : Mass.PhysicalMassInterlacing

    gapProducesPhysicalInterlacing :
      Positive reconstructedTheory (spectralGap reconstructedTheory) →
      Mass.PhysicalMassInterlacing

    interlacingAgrees :
      gapProducesPhysicalInterlacing
        (spectralGapPositive reconstructedTheory)
      ≡ physicalInterlacing

open PhysicalContinuumOSGapData public

continuumOSAxiomsFromPhysicalClosure :
  ∀ {State Bound Measure Observable Schwinger Scalar Hilbert Vector}
    (dataSet : PhysicalContinuumOSGapData
      State Bound Measure Observable Schwinger Scalar Hilbert Vector) →
  Existing.ContinuumOSAxioms (continuumClosure dataSet)
continuumOSAxiomsFromPhysicalClosure dataSet =
  Existing.assembleContinuumOSAxioms (continuumClosure dataSet)

physicalGramReflectionPositiveAtClosure :
  ∀ {State Bound Measure Observable Schwinger Scalar Hilbert Vector}
    (dataSet : PhysicalContinuumOSGapData
      State Bound Measure Observable Schwinger Scalar Hilbert Vector) →
  OS.GramReflectionPositive
    (Physical.physicalMeasureTopologyControlsOSGram
      (physicalGramData dataSet))
    (Limit.continuumMeasure (continuumClosure dataSet))
physicalGramReflectionPositiveAtClosure dataSet =
  subst
    (OS.GramReflectionPositive
      (Physical.physicalMeasureTopologyControlsOSGram
        (physicalGramData dataSet)))
    (physicalContinuumMeasureAgrees dataSet)
    (Physical.physicalContinuumReflectionPositive
      (physicalGramData dataSet))

physicalContinuumReflectionPositive :
  ∀ {State Bound Measure Observable Schwinger Scalar Hilbert Vector}
    (dataSet : PhysicalContinuumOSGapData
      State Bound Measure Observable Schwinger Scalar Hilbert Vector) →
  Limit.ReflectionPositive (continuumClosure dataSet)
    (Limit.schwinger (continuumClosure dataSet)
      (Limit.continuumMeasure (continuumClosure dataSet)))
physicalContinuumReflectionPositive dataSet =
  gramReflectionImpliesClosureReflection dataSet
    (physicalGramReflectionPositiveAtClosure dataSet)

constructedPhysicalMassTransport :
  ∀ {State Bound Measure Observable Schwinger Scalar Hilbert Vector}
    (dataSet : PhysicalContinuumOSGapData
      State Bound Measure Observable Schwinger Scalar Hilbert Vector) →
  Mass.survivingMass (physicalInterlacing dataSet)
  ≤ Mass.physicalGap (physicalInterlacing dataSet) zero
constructedPhysicalMassTransport dataSet =
  Mass.positivePhysicalMassSurvives (physicalInterlacing dataSet)

physicalMeasurePresentationAgreementLevel : ProofLevel
physicalMeasurePresentationAgreementLevel = machineChecked

physicalMeasureToGramClosureReuseLevel : ProofLevel
physicalMeasureToGramClosureReuseLevel = machineChecked

physicalContinuumReflectionPositivityAssemblyLevel : ProofLevel
physicalContinuumReflectionPositivityAssemblyLevel = machineChecked

physicalContinuumOSAxiomAssemblyLevel : ProofLevel
physicalContinuumOSAxiomAssemblyLevel = machineChecked

physicalGapToInterlacingAssemblyLevel : ProofLevel
physicalGapToInterlacingAssemblyLevel = machineChecked

physicalUVToContinuumMeasureInputsLevel : ProofLevel
physicalUVToContinuumMeasureInputsLevel = conditional

physicalExpectationConvergenceInputsLevel : ProofLevel
physicalExpectationConvergenceInputsLevel = conditional

physicalGramToClosureReflectionMeaningInputsLevel : ProofLevel
physicalGramToClosureReflectionMeaningInputsLevel = conditional

uniformClusteringOS4InputsLevel : ProofLevel
uniformClusteringOS4InputsLevel = conditional

fullO4CovarianceOS1InputsLevel : ProofLevel
fullO4CovarianceOS1InputsLevel = conditional

clusteringToPositiveTransferGapInputsLevel : ProofLevel
clusteringToPositiveTransferGapInputsLevel = conditional
