module DASHI.Physics.YangMills.BalabanClayConcreteUVToMassGapDependencyExact where

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4CombinedRGUVIterationExact as UV
import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMassTransportExact as Mass

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
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
-- This module replaces an arbitrary four-Set dependency receipt with the actual
-- DASHI UV, continuum-OS and physical-interlacing record types. It does not
-- manufacture the thermodynamic/continuum limit, OS reconstruction theorem or
-- clustering-to-gap theorem; those remain precisely typed bridge functions.
------------------------------------------------------------------------

record ContinuumOSAxioms
    {Measure Schwinger : Set}
    (closure : Limit.FiniteToContinuumOSClosure Measure Schwinger) : Set where
  field
    normalized :
      Limit.Normalized closure (Limit.continuumMeasure closure)
    positive :
      Limit.Positive closure (Limit.continuumMeasure closure)
    gaugeInvariant :
      Limit.GaugeInvariant closure (Limit.continuumMeasure closure)

    euclideanCovariant :
      Limit.EuclideanCovariant closure
        (Limit.schwinger closure (Limit.continuumMeasure closure))
    reflectionPositive :
      Limit.ReflectionPositive closure
        (Limit.schwinger closure (Limit.continuumMeasure closure))
    symmetric :
      Limit.Symmetric closure
        (Limit.schwinger closure (Limit.continuumMeasure closure))
    tempered :
      Limit.Tempered closure
        (Limit.schwinger closure (Limit.continuumMeasure closure))
    regular :
      Limit.Regular closure
        (Limit.schwinger closure (Limit.continuumMeasure closure))
    clustered :
      Limit.Clustered closure
        (Limit.schwinger closure (Limit.continuumMeasure closure))

open ContinuumOSAxioms public

assembleContinuumOSAxioms :
  ∀ {Measure Schwinger}
    (closure : Limit.FiniteToContinuumOSClosure Measure Schwinger) →
  ContinuumOSAxioms closure
assembleContinuumOSAxioms closure = record
  { normalized = Limit.continuumNormalized closure
  ; positive = Limit.continuumPositive closure
  ; gaugeInvariant = Limit.continuumGaugeInvariant closure
  ; euclideanCovariant = Limit.continuumEuclideanCovariant closure
  ; reflectionPositive = Limit.continuumReflectionPositive closure
  ; symmetric = Limit.continuumSymmetric closure
  ; tempered = Limit.continuumTempered closure
  ; regular = Limit.continuumRegular closure
  ; clustered = Limit.continuumClustered closure
  }

record ConcreteUVToMassGapDependency
    (State Bound Measure Schwinger HilbertTheory : Set) : Set₁ where
  field
    uvPackage : UV.Gate4UVCompletionPackage State Bound

    continuumFromAllScaleUV :
      ((scale : Nat) →
        UV.AdmissibleRGState (UV.admissibility uvPackage)
          (UV.stateAt (UV.normData uvPackage)
            (UV.initial uvPackage) scale)) →
      Limit.FiniteToContinuumOSClosure Measure Schwinger

    reconstruct :
      (closure : Limit.FiniteToContinuumOSClosure Measure Schwinger) →
      ContinuumOSAxioms closure → HilbertTheory

    SpectralGap : HilbertTheory → Set

    clusteredOSReconstructionHasGap :
      (closure : Limit.FiniteToContinuumOSClosure Measure Schwinger) →
      (axioms : ContinuumOSAxioms closure) →
      SpectralGap (reconstruct closure axioms)

    physicalInterlacingFromGap :
      (theory : HilbertTheory) →
      SpectralGap theory → Mass.PhysicalMassInterlacing

open ConcreteUVToMassGapDependency public

constructedContinuum :
  ∀ {State Bound Measure Schwinger HilbertTheory} →
  ConcreteUVToMassGapDependency State Bound Measure Schwinger HilbertTheory →
  Limit.FiniteToContinuumOSClosure Measure Schwinger
constructedContinuum dataSet =
  continuumFromAllScaleUV dataSet
    (UV.packageAllScaleAdmissible (uvPackage dataSet))

constructedOSAxioms :
  ∀ {State Bound Measure Schwinger HilbertTheory}
    (dataSet : ConcreteUVToMassGapDependency
      State Bound Measure Schwinger HilbertTheory) →
  ContinuumOSAxioms (constructedContinuum dataSet)
constructedOSAxioms dataSet =
  assembleContinuumOSAxioms (constructedContinuum dataSet)

constructedHilbertTheory :
  ∀ {State Bound Measure Schwinger HilbertTheory} →
  ConcreteUVToMassGapDependency State Bound Measure Schwinger HilbertTheory →
  HilbertTheory
constructedHilbertTheory dataSet =
  reconstruct dataSet
    (constructedContinuum dataSet)
    (constructedOSAxioms dataSet)

constructedSpectralGap :
  ∀ {State Bound Measure Schwinger HilbertTheory}
    (dataSet : ConcreteUVToMassGapDependency
      State Bound Measure Schwinger HilbertTheory) →
  SpectralGap dataSet (constructedHilbertTheory dataSet)
constructedSpectralGap dataSet =
  clusteredOSReconstructionHasGap dataSet
    (constructedContinuum dataSet)
    (constructedOSAxioms dataSet)

constructedPhysicalMassInterlacing :
  ∀ {State Bound Measure Schwinger HilbertTheory}
    (dataSet : ConcreteUVToMassGapDependency
      State Bound Measure Schwinger HilbertTheory) →
  Mass.PhysicalMassInterlacing
constructedPhysicalMassInterlacing dataSet =
  physicalInterlacingFromGap dataSet
    (constructedHilbertTheory dataSet)
    (constructedSpectralGap dataSet)

constructedPositivePhysicalMassTransport :
  ∀ {State Bound Measure Schwinger HilbertTheory}
    (dataSet : ConcreteUVToMassGapDependency
      State Bound Measure Schwinger HilbertTheory) →
  Mass.survivingMass (constructedPhysicalMassInterlacing dataSet)
  Data.Rational._≤_
    Mass.physicalGap (constructedPhysicalMassInterlacing dataSet)
      Agda.Builtin.Nat.zero
constructedPositivePhysicalMassTransport dataSet =
  Mass.positivePhysicalMassSurvives
    (constructedPhysicalMassInterlacing dataSet)

continuumOSAxiomAssemblyLevel : ProofLevel
continuumOSAxiomAssemblyLevel = machineChecked

concreteUVToMassGapDependencyAssemblyLevel : ProofLevel
concreteUVToMassGapDependencyAssemblyLevel = machineChecked

-- The remaining inputs are actual theorem bridges, not arbitrary proposition
-- names: all-scale UV to the continuum closure, OS reconstruction plus clustering
-- to a spectral gap, and spectral gap to the physical interlacing package.
allScaleUVToContinuumClosureInputsLevel : ProofLevel
allScaleUVToContinuumClosureInputsLevel = conditional

osReconstructionAndClusteringToGapInputsLevel : ProofLevel
osReconstructionAndClusteringToGapInputsLevel = conditional

spectralGapToPhysicalInterlacingInputsLevel : ProofLevel
spectralGapToPhysicalInterlacingInputsLevel = conditional
