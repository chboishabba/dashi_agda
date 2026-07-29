module DASHI.Physics.YangMills.BalabanClayT5PhysicalContinuumOSGapBridgeExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Rational using (_≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4CombinedRGUVIterationExact as UV
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Physical
import DASHI.Physics.YangMills.BalabanClayT5OSGramClosedPropertyExact as Gram
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
    (State Bound Measure Observable Schwinger Scalar
      TestFamily Hilbert Vector : Set) : Set₁ where
  field
    uvPackage : UV.Gate4UVCompletionPackage State Bound

    physicalMeasureConvergence :
      Physical.PhysicalMeasureConvergenceData Measure Observable Scalar

    continuumClosure : Limit.FiniteToContinuumOSClosure Measure Schwinger

    physicalMeasureSequenceAgrees : ∀ cutoff →
      Physical.measureSequence physicalMeasureConvergence cutoff
      ≡ Limit.finiteMeasures continuumClosure cutoff

    physicalContinuumMeasureAgrees :
      Physical.continuumMeasure physicalMeasureConvergence
      ≡ Limit.continuumMeasure continuumClosure

    gramTopology :
      Gram.MeasureTopologyControlsOSGram Measure Schwinger TestFamily Scalar

    measureLimitAgrees :
      Gram.measureLimit gramTopology ≡ Limit.measureLimit continuumClosure

    finiteReflectionPositive : ∀ cutoff →
      Gram.MeasureReflectionPositive gramTopology
        (Limit.finiteMeasures continuumClosure cutoff)

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
  ∀ {State Bound Measure Observable Schwinger Scalar
      TestFamily Hilbert Vector}
    (dataSet : PhysicalContinuumOSGapData
      State Bound Measure Observable Schwinger Scalar
      TestFamily Hilbert Vector) →
  Existing.ContinuumOSAxioms (continuumClosure dataSet)
continuumOSAxiomsFromPhysicalClosure dataSet =
  Existing.assembleContinuumOSAxioms (continuumClosure dataSet)

continuumReflectionPositiveFromGramTopology :
  ∀ {State Bound Measure Observable Schwinger Scalar
      TestFamily Hilbert Vector}
    (dataSet : PhysicalContinuumOSGapData
      State Bound Measure Observable Schwinger Scalar
      TestFamily Hilbert Vector) →
  Gram.MeasureReflectionPositive (gramTopology dataSet)
    (Limit.continuumMeasure (continuumClosure dataSet))
continuumReflectionPositiveFromGramTopology dataSet =
  Gram.measureReflectionPositiveClosed
    (gramTopology dataSet)
    (Limit.finiteMeasures (continuumClosure dataSet))
    (Limit.continuumMeasure (continuumClosure dataSet))
    (transportConvergence
      (measureLimitAgrees dataSet)
      (Limit.continuumIsLimit (continuumClosure dataSet)))
    (finiteReflectionPositive dataSet)
  where
  transportConvergence :
    ∀ {Measure : Set}
      {left right : Limit.SequentialLimit Measure}
      {sequence target} →
    left ≡ right →
    Limit.Converges right sequence target →
    Limit.Converges left sequence target
  transportConvergence refl proof = proof

constructedPhysicalMassTransport :
  ∀ {State Bound Measure Observable Schwinger Scalar
      TestFamily Hilbert Vector}
    (dataSet : PhysicalContinuumOSGapData
      State Bound Measure Observable Schwinger Scalar
      TestFamily Hilbert Vector) →
  Mass.survivingMass (physicalInterlacing dataSet)
  ≤ Mass.physicalGap (physicalInterlacing dataSet) zero
constructedPhysicalMassTransport dataSet =
  Mass.positivePhysicalMassSurvives (physicalInterlacing dataSet)

physicalMeasurePresentationAgreementLevel : ProofLevel
physicalMeasurePresentationAgreementLevel = machineChecked

physicalMeasureToGramClosureAssemblyLevel : ProofLevel
physicalMeasureToGramClosureAssemblyLevel = machineChecked

physicalContinuumOSAxiomAssemblyLevel : ProofLevel
physicalContinuumOSAxiomAssemblyLevel = machineChecked

physicalGapToInterlacingAssemblyLevel : ProofLevel
physicalGapToInterlacingAssemblyLevel = machineChecked

physicalUVToContinuumMeasureInputsLevel : ProofLevel
physicalUVToContinuumMeasureInputsLevel = conditional

physicalMeasureToGramTopologyInputsLevel : ProofLevel
physicalMeasureToGramTopologyInputsLevel = conditional

uniformClusteringOS4InputsLevel : ProofLevel
uniformClusteringOS4InputsLevel = conditional

fullO4CovarianceOS1InputsLevel : ProofLevel
fullO4CovarianceOS1InputsLevel = conditional

clusteringToPositiveTransferGapInputsLevel : ProofLevel
clusteringToPositiveTransferGapInputsLevel = conditional
