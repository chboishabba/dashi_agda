module DASHI.Physics.YangMills.BalabanClayGate4CoarsePartitionWitnessExact where

------------------------------------------------------------------------
-- PHYSICAL GATE4 COARSE PARTITION + ONE POSITIVE STATE PER FIBRE
--   -> FINITE COARSE PARTITION WITH POSITIVE MASSES
--
-- The normalized Gate4 fine law is already nonnegative by compiler theorem.
-- Therefore positivity of each retained coarse mass needs only one positive
-- fine-state witness in that coarse fibre.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; Positive)
open import Agda.Builtin.List using (List)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteProbabilityPartitionDisintegrationExact as Partition
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4PreferredRationalReferenceNormalizationExact as Reference
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceToFiniteRGProbabilityExact as Probability
import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibrePositiveMassExact as PositiveMass

record Gate4CoarsePartitionWitnessData
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

    coarseStates : List Coarse
    project : Fine → Coarse
    matches : Coarse → Fine → Bool

    Match : Coarse → Fine → Set
    matchTrue : ∀ coarse fine →
      matches coarse fine ≡ true → Match coarse fine
    matchProjects : ∀ {coarse fine} →
      Match coarse fine → project fine ≡ coarse

    partitionOfUnity : ∀ fine →
      DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact.sumRational
        coarseStates
        (λ coarse → Partition.indicator (matches coarse fine))
      ≡ Data.Rational.Base.1ℚ

    positiveWitness : Coarse → Fine

    positiveWitnessInStates : ∀ coarse →
      PositiveMass._∈_
        (positiveWitness coarse)
        (T.fastFibre
          (PhysicalT.canonicalPhysicalTData construction)
          scale component)

    positiveWitnessMatches : ∀ coarse →
      matches coarse (positiveWitness coarse) ≡ true

    positiveWitnessWeight : ∀ coarse →
      Positive
        (Probability.selectedReferenceProbabilityWeight
          (Reference.compilePreferredRationalReferenceNormalization
            referenceInputs)
          scale component slow
          (positiveWitness coarse))

open Gate4CoarsePartitionWitnessData public

compileGate4FiniteCoarsePartitionWitness :
  ∀ {Scale Fine SlowField Component Functional Coarse}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Reference.PreferredRationalReferenceNormalizationInputs
        {construction = construction}} →
  Gate4CoarsePartitionWitnessData referenceInputs →
  Partition.FiniteCoarsePartitionWitness
    (T.fastFibre
      (PhysicalT.canonicalPhysicalTData construction)
      (scale _) (component _))
    (Probability.selectedReferenceProbabilityWeight
      (Reference.compilePreferredRationalReferenceNormalization
        referenceInputs)
      (scale _) (component _) (slow _))
compileGate4FiniteCoarsePartitionWitness
  {referenceInputs = referenceInputs} dataSet = record
  { coarseStates = coarseStates dataSet
  ; project = project dataSet
  ; matches = matches dataSet
  ; Match = Match dataSet
  ; matchTrue = matchTrue dataSet
  ; matchProjects = matchProjects dataSet
  ; partitionOfUnity = partitionOfUnity dataSet
  ; fineWeightNonnegative = λ fine →
      Probability.selectedReferenceProbabilityWeightNonnegative
        (Reference.preferredRationalReferenceFoldSemantics referenceInputs)
        (scale dataSet) (component dataSet) (slow dataSet) fine
  ; positiveWitness = positiveWitness dataSet
  ; positiveWitnessInStates = positiveWitnessInStates dataSet
  ; positiveWitnessMatches = positiveWitnessMatches dataSet
  ; positiveWitnessWeight = positiveWitnessWeight dataSet
  }

compileGate4FiniteCoarsePartition :
  ∀ {Scale Fine SlowField Component Functional Coarse}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Reference.PreferredRationalReferenceNormalizationInputs
        {construction = construction}}
    (dataSet : Gate4CoarsePartitionWitnessData referenceInputs) →
  Partition.FiniteCoarsePartition
    (T.fastFibre
      (PhysicalT.canonicalPhysicalTData construction)
      (scale dataSet) (component dataSet))
    (Probability.selectedReferenceProbabilityWeight
      (Reference.compilePreferredRationalReferenceNormalization
        referenceInputs)
      (scale dataSet) (component dataSet) (slow dataSet))
compileGate4FiniteCoarsePartition dataSet =
  Partition.compileFiniteCoarsePartition
    (compileGate4FiniteCoarsePartitionWitness dataSet)

gate4FineNonnegativeToCoarseMassCompilerLevel : ProofLevel
gate4FineNonnegativeToCoarseMassCompilerLevel = machineChecked

gate4CoarsePartitionWitnessCompilerLevel : ProofLevel
gate4CoarsePartitionWitnessCompilerLevel = machineChecked

-- Remaining physical data are now discrete partition/support facts.
gate4CoarsePartitionGeometryLevel : ProofLevel
gate4CoarsePartitionGeometryLevel = conditional

gate4PositiveStatePerCoarseFibreLevel : ProofLevel
gate4PositiveStatePerCoarseFibreLevel = conditional
