module DASHI.Physics.YangMills.BalabanFiniteVolumePartitionedGate4PresentationExact where

------------------------------------------------------------------------
-- CUTOFF-INDEXED PHYSICAL COARSE PARTITION
--   -> CANONICAL ROUND283 / SELECTED PROBABILITY PRESENTATION
--
-- The preferred finite RG route now supplies only the physical coarse
-- partition at each cutoff.  Coarse weights, conditional kernels, kernel
-- normalization, disintegration, reopening steps and probability laws are all
-- compiler output.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5PreferredDiagonalExpectationProducerExact as Diagonal
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4PreferredRationalReferenceNormalizationExact as Reference
import DASHI.Physics.YangMills.BalabanClayGate4PartitionedFiniteRGReopeningExact as Partitioned
import DASHI.Physics.YangMills.BalabanFiniteVolumeCanonicalGate4PresentationExact as Canonical
import DASHI.Physics.YangMills.BalabanFiniteRGProbabilityExpectationSemanticsExact as Probability
import DASHI.Physics.YangMills.BalabanFiniteVolumeReopeningPresentationRound283Exact as R283

record PartitionedGate4FiniteVolumePresentationInputs
    {Scale Fine SlowField Component Functional Coarse Measure : Set}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    (referenceInputs :
      Reference.PreferredRationalReferenceNormalizationInputs
        {construction = construction})
    (thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ) : Set₁ where
  field
    coarsePartitionAt : Nat →
      Partitioned.CanonicalGate4CoarsePartitionData referenceInputs

    finiteVolumeExpectationIsPartitionedReopeningExpectation :
      ∀ cutoff observable →
      Gram.expectation (T5.operations thermodynamic)
        (Diagonal.selectedFiniteVolumeSequence thermodynamic cutoff)
        observable
      ≡
      Reopen.fineExpectation
        (Partitioned.partitionedGate4ReopeningStep
          (coarsePartitionAt cutoff))
        observable

open PartitionedGate4FiniteVolumePresentationInputs public

asCanonicalGate4FiniteVolumePresentationInputs :
  ∀ {Scale Fine SlowField Component Functional Coarse Measure}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Reference.PreferredRationalReferenceNormalizationInputs
        {construction = construction}}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ} →
  PartitionedGate4FiniteVolumePresentationInputs
    referenceInputs thermodynamic →
  Canonical.CanonicalGate4FiniteVolumePresentationInputs
    referenceInputs thermodynamic
asCanonicalGate4FiniteVolumePresentationInputs inputs = record
  { reopeningDataAt = λ cutoff →
      Partitioned.compileCanonicalGate4ReopeningData
        (coarsePartitionAt inputs cutoff)
  ; finiteVolumeExpectationIsCanonicalReopeningExpectation =
      finiteVolumeExpectationIsPartitionedReopeningExpectation inputs
  }

compilePartitionedGate4Round283Presentation :
  ∀ {Scale Fine SlowField Component Functional Coarse Measure}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Reference.PreferredRationalReferenceNormalizationInputs
        {construction = construction}}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ} →
  PartitionedGate4FiniteVolumePresentationInputs
    referenceInputs thermodynamic →
  R283.FiniteVolumeReopeningPresentation
    Measure Fine Coarse thermodynamic
compilePartitionedGate4Round283Presentation inputs =
  Canonical.compileCanonicalGate4Round283Presentation
    (asCanonicalGate4FiniteVolumePresentationInputs inputs)

compilePartitionedGate4SelectedT5ProbabilityPresentation :
  ∀ {Scale Fine SlowField Component Functional Coarse Measure}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Reference.PreferredRationalReferenceNormalizationInputs
        {construction = construction}}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ} →
  PartitionedGate4FiniteVolumePresentationInputs
    referenceInputs thermodynamic →
  Probability.SelectedT5FiniteProbabilityPresentation
    Measure Fine Coarse thermodynamic
compilePartitionedGate4SelectedT5ProbabilityPresentation inputs =
  Canonical.compileCanonicalGate4SelectedT5ProbabilityPresentation
    (asCanonicalGate4FiniteVolumePresentationInputs inputs)

partitionedGate4Round283CompilerLevel : ProofLevel
partitionedGate4Round283CompilerLevel = machineChecked

partitionedGate4SelectedProbabilityCompilerLevel : ProofLevel
partitionedGate4SelectedProbabilityCompilerLevel = machineChecked

-- Surviving physical finite inputs:
--  * actual cutoff-indexed coarse partition geometry,
--  * exact selected T5 expectation identity against the constructed law.
physicalCoarsePartitionFamilyLevel : ProofLevel
physicalCoarsePartitionFamilyLevel = conditional

finiteExpectationPartitionedReopeningSameObjectLevel : ProofLevel
finiteExpectationPartitionedReopeningSameObjectLevel = conditional
