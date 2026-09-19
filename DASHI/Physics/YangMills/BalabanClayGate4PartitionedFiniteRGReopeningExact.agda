module DASHI.Physics.YangMills.BalabanClayGate4PartitionedFiniteRGReopeningExact where

------------------------------------------------------------------------
-- GATE4 NORMALIZED FINE LAW + PHYSICAL COARSE PARTITION
--   -> CANONICAL FINITE RG REOPENING
--
-- The generic finite conditionalization theorem constructs:
--
--   coarseWeight(y) = sum_{x in fibre y} fineWeight(x)
--   kappa(y,x)       = coarseWeight(y)^(-1) fineWeight(x)  on the fibre
--
-- and proves both fibre normalization and exact fine/coarse disintegration.
--
-- Hence the preferred Gate4 reopening no longer asks for coarse weights,
-- reopening kernels, kernel normalization or disintegration as independent
-- physical fields.  It asks only for the actual finite coarse partition of the
-- selected Gate4 fast-state list.
------------------------------------------------------------------------

open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteProbabilityPartitionDisintegrationExact as Partition
import DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanFiniteRGProbabilityExpectationSemanticsExact as FiniteProbability
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4PreferredRationalReferenceNormalizationExact as Reference
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceToFiniteRGProbabilityExact as Probability
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalFiniteRGReopeningExact as Reopening
import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T

record CanonicalGate4CoarsePartitionData
    {Scale Fine SlowField Component Functional Coarse : Set}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    (referenceInputs :
      Reference.PreferredRationalReferenceNormalizationInputs
        {construction = construction}) : Set₁ where
  field
    scale : Scale
    component : Component
    slow : SlowField

    partition :
      Partition.FiniteCoarsePartition
        (T.fastFibre
          (PhysicalT.canonicalPhysicalTData construction)
          scale component)
        (Probability.selectedReferenceProbabilityWeight
          (Reference.compilePreferredRationalReferenceNormalization
            referenceInputs)
          scale component slow)

open CanonicalGate4CoarsePartitionData public

compileCanonicalGate4ReopeningData :
  ∀ {Scale Fine SlowField Component Functional Coarse}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Reference.PreferredRationalReferenceNormalizationInputs
        {construction = construction}} →
  CanonicalGate4CoarsePartitionData referenceInputs →
  Reopening.CanonicalGate4ReopeningData referenceInputs
compileCanonicalGate4ReopeningData dataSet =
  let
    p = partition dataSet
  in
  record
    { scale = scale dataSet
    ; component = component dataSet
    ; slow = slow dataSet
    ; coarseStates = Partition.coarseStates p
    ; project = Partition.project p
    ; coarseWeight = Partition.coarseMass p
    ; reopeningKernel = Partition.conditionalKernel p
    ; FibreSupport = Partition.Match p
    ; fibreSupportProjects = Partition.matchProjects p
    ; reopeningOffFibreZero =
        Partition.conditionalKernelOffFibreZero p
    ; reopeningNormalized =
        Partition.conditionalKernelNormalized p
    ; disintegrationExact =
        Partition.conditionalDisintegrationExact p
    }

partitionedGate4ReopeningStep :
  ∀ {Scale Fine SlowField Component Functional Coarse}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Reference.PreferredRationalReferenceNormalizationInputs
        {construction = construction}} →
  CanonicalGate4CoarsePartitionData referenceInputs →
  Reopen.FiniteRGReopeningStep
    Fine Coarse
partitionedGate4ReopeningStep dataSet =
  Reopening.canonicalGate4ReopeningStep
    (compileCanonicalGate4ReopeningData dataSet)

partitionedGate4ProbabilityLaw :
  ∀ {Scale Fine SlowField Component Functional Coarse}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Reference.PreferredRationalReferenceNormalizationInputs
        {construction = construction}}
    (dataSet : CanonicalGate4CoarsePartitionData referenceInputs) →
  FiniteProbability.FiniteRGProbabilityLaw
    (partitionedGate4ReopeningStep dataSet)
partitionedGate4ProbabilityLaw dataSet =
  Reopening.canonicalGate4ReopeningProbabilityLaw
    (compileCanonicalGate4ReopeningData dataSet)

gate4PartitionToReopeningDataCompilerLevel : ProofLevel
gate4PartitionToReopeningDataCompilerLevel = machineChecked

gate4PartitionToReopeningStepCompilerLevel : ProofLevel
gate4PartitionToReopeningStepCompilerLevel = machineChecked

gate4PartitionToProbabilityLawCompilerLevel : ProofLevel
gate4PartitionToProbabilityLawCompilerLevel = machineChecked

-- Remaining finite RG input is now partition geometry, not measure algebra:
-- coverage/uniqueness of the selected coarse fibres, agreement with the
-- physical block projection, and positivity of each retained coarse fibre.
physicalGate4CoarsePartitionLevel : ProofLevel
physicalGate4CoarsePartitionLevel = conditional
