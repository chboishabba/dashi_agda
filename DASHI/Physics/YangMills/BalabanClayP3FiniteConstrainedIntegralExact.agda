module DASHI.Physics.YangMills.BalabanClayP3FiniteConstrainedIntegralExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayP3PhysicalOneStepTransferExact as P3

------------------------------------------------------------------------
-- Exact constrained finite integration.
--
-- This is the literal algebra needed by every finite quadrature/character
-- truncation of the Haar integral.  The full constrained sum is defined
-- independently of the small/large split, and the partition theorem is proved
-- from the commutative-monoid interchange law rather than installed as a field.
------------------------------------------------------------------------

record FiniteConstrainedSum
    (Fine Coarse Scalar : Set) : Set₁ where
  field
    fineFields : List Fine
    blockMap : Fine → Coarse
    coarseMatches : Fine → Coarse → Bool
    coarseMatchesSound : ∀ field coarse →
      coarseMatches field coarse ≡ true → blockMap field ≡ coarse
    coarseMatchesComplete : ∀ field coarse →
      blockMap field ≡ coarse → coarseMatches field coarse ≡ true

    isSmall : Fine → Bool
    weight : Fine → Scalar

    zero : Scalar
    add : Scalar → Scalar → Scalar
    addZeroLeft : ∀ value → add zero value ≡ value
    addZeroRight : ∀ value → add value zero ≡ value
    interchange : ∀ first second third fourth →
      add (add first second) (add third fourth)
      ≡ add (add first third) (add second fourth)

open FiniteConstrainedSum public

selectedWith :
  ∀ {Fine Coarse Scalar} →
  FiniteConstrainedSum Fine Coarse Scalar →
  (Fine → Scalar) → Coarse → Fine → Scalar
selectedWith dataSet weightFunction coarse field
  with coarseMatches dataSet field coarse
... | true = weightFunction field
... | false = zero dataSet

smallSelectedWith :
  ∀ {Fine Coarse Scalar} →
  FiniteConstrainedSum Fine Coarse Scalar →
  (Fine → Scalar) → Coarse → Fine → Scalar
smallSelectedWith dataSet weightFunction coarse field
  with isSmall dataSet field
... | true = selectedWith dataSet weightFunction coarse field
... | false = zero dataSet

largeSelectedWith :
  ∀ {Fine Coarse Scalar} →
  FiniteConstrainedSum Fine Coarse Scalar →
  (Fine → Scalar) → Coarse → Fine → Scalar
largeSelectedWith dataSet weightFunction coarse field
  with isSmall dataSet field
... | true = zero dataSet
... | false = selectedWith dataSet weightFunction coarse field

selectedSplits :
  ∀ {Fine Coarse Scalar}
    (dataSet : FiniteConstrainedSum Fine Coarse Scalar)
    weightFunction coarse field →
  selectedWith dataSet weightFunction coarse field
  ≡ add dataSet
      (smallSelectedWith dataSet weightFunction coarse field)
      (largeSelectedWith dataSet weightFunction coarse field)
selectedSplits dataSet weightFunction coarse field
  with isSmall dataSet field
... | true = sym (addZeroRight dataSet
    (selectedWith dataSet weightFunction coarse field))
... | false = sym (addZeroLeft dataSet
    (selectedWith dataSet weightFunction coarse field))

foldSelected :
  ∀ {Fine Coarse Scalar} →
  FiniteConstrainedSum Fine Coarse Scalar →
  (Fine → Scalar) → Coarse → List Fine → Scalar
foldSelected dataSet selector coarse [] = zero dataSet
foldSelected dataSet selector coarse (field ∷ fields) =
  add dataSet (selector field)
    (foldSelected dataSet selector coarse fields)

constrainedIntegral :
  ∀ {Fine Coarse Scalar} →
  FiniteConstrainedSum Fine Coarse Scalar →
  List Fine → (Fine → Scalar) → Coarse → Scalar
constrainedIntegral dataSet fields weightFunction coarse =
  foldSelected dataSet
    (selectedWith dataSet weightFunction coarse)
    coarse fields

smallFieldContribution :
  ∀ {Fine Coarse Scalar} →
  FiniteConstrainedSum Fine Coarse Scalar →
  List Fine → (Fine → Scalar) → Coarse → Scalar
smallFieldContribution dataSet fields weightFunction coarse =
  foldSelected dataSet
    (smallSelectedWith dataSet weightFunction coarse)
    coarse fields

largeFieldContribution :
  ∀ {Fine Coarse Scalar} →
  FiniteConstrainedSum Fine Coarse Scalar →
  List Fine → (Fine → Scalar) → Coarse → Scalar
largeFieldContribution dataSet fields weightFunction coarse =
  foldSelected dataSet
    (largeSelectedWith dataSet weightFunction coarse)
    coarse fields

smallLargePartitionListExact :
  ∀ {Fine Coarse Scalar}
    (dataSet : FiniteConstrainedSum Fine Coarse Scalar)
    fields weightFunction coarse →
  constrainedIntegral dataSet fields weightFunction coarse
  ≡ add dataSet
      (smallFieldContribution dataSet fields weightFunction coarse)
      (largeFieldContribution dataSet fields weightFunction coarse)
smallLargePartitionListExact dataSet [] weightFunction coarse =
  sym (addZeroLeft dataSet (zero dataSet))
smallLargePartitionListExact dataSet (field ∷ fields) weightFunction coarse =
  trans
    (cong
      (add dataSet
        (selectedWith dataSet weightFunction coarse field))
      (smallLargePartitionListExact dataSet fields weightFunction coarse))
    (trans
      (cong
        (λ value → add dataSet value
          (add dataSet
            (smallFieldContribution dataSet fields weightFunction coarse)
            (largeFieldContribution dataSet fields weightFunction coarse)))
        (selectedSplits dataSet weightFunction coarse field))
      (interchange dataSet
        (smallSelectedWith dataSet weightFunction coarse field)
        (largeSelectedWith dataSet weightFunction coarse field)
        (smallFieldContribution dataSet fields weightFunction coarse)
        (largeFieldContribution dataSet fields weightFunction coarse)))

smallLargePartitionExact :
  ∀ {Fine Coarse Scalar}
    (dataSet : FiniteConstrainedSum Fine Coarse Scalar)
    coarse →
  constrainedIntegral dataSet (fineFields dataSet) (weight dataSet) coarse
  ≡ add dataSet
      (smallFieldContribution dataSet
        (fineFields dataSet) (weight dataSet) coarse)
      (largeFieldContribution dataSet
        (fineFields dataSet) (weight dataSet) coarse)
smallLargePartitionExact dataSet coarse =
  smallLargePartitionListExact dataSet
    (fineFields dataSet) (weight dataSet) coarse

------------------------------------------------------------------------
-- Exact finite effective action and adapter to the P3 one-step surface.
------------------------------------------------------------------------

record FiniteEffectiveAction
    (Fine Coarse Scalar EffectiveAction : Set) : Set₁ where
  field
    sumData : FiniteConstrainedSum Fine Coarse Scalar
    vacuumNormalization : Scalar
    multiply : Scalar → Scalar → Scalar
    negativeLog : Scalar → EffectiveAction
    exponentialOfNegativeAction : EffectiveAction → Scalar
    exponentialNegativeLog : ∀ scalar →
      exponentialOfNegativeAction (negativeLog scalar) ≡ scalar

open FiniteEffectiveAction public

nextEffectiveAction :
  ∀ {Fine Coarse Scalar EffectiveAction} →
  FiniteEffectiveAction Fine Coarse Scalar EffectiveAction →
  Coarse → EffectiveAction
nextEffectiveAction dataSet coarse =
  negativeLog dataSet
    (multiply dataSet (vacuumNormalization dataSet)
      (constrainedIntegral (sumData dataSet)
        (fineFields (sumData dataSet))
        (weight (sumData dataSet)) coarse))

effectiveActionDefinesIntegral :
  ∀ {Fine Coarse Scalar EffectiveAction}
    (dataSet : FiniteEffectiveAction Fine Coarse Scalar EffectiveAction)
    coarse →
  exponentialOfNegativeAction dataSet (nextEffectiveAction dataSet coarse)
  ≡ multiply dataSet (vacuumNormalization dataSet)
      (constrainedIntegral (sumData dataSet)
        (fineFields (sumData dataSet))
        (weight (sumData dataSet)) coarse)
effectiveActionDefinesIntegral dataSet coarse =
  exponentialNegativeLog dataSet _

finiteExactOneStepIntegral :
  ∀ {Fine Coarse Scalar EffectiveAction} →
  FiniteEffectiveAction Fine Coarse Scalar EffectiveAction →
  P3.ExactOneStepIntegral
    Fine Coarse (List Fine) Scalar EffectiveAction Scalar
finiteExactOneStepIntegral dataSet = record
  { P3.ExactOneStepIntegral.blockMap = blockMap (sumData dataSet)
  ; P3.ExactOneStepIntegral.fineMeasure = fineFields (sumData dataSet)
  ; P3.ExactOneStepIntegral.boltzmannWeight = weight (sumData dataSet)
  ; P3.ExactOneStepIntegral.constrainedIntegral =
      constrainedIntegral (sumData dataSet)
  ; P3.ExactOneStepIntegral.nextEffectiveAction = nextEffectiveAction dataSet
  ; P3.ExactOneStepIntegral.exponentialOfNegativeAction =
      exponentialOfNegativeAction dataSet
  ; P3.ExactOneStepIntegral.smallFieldContribution =
      smallFieldContribution (sumData dataSet)
        (fineFields (sumData dataSet)) (weight (sumData dataSet))
  ; P3.ExactOneStepIntegral.largeFieldContribution =
      largeFieldContribution (sumData dataSet)
        (fineFields (sumData dataSet)) (weight (sumData dataSet))
  ; P3.ExactOneStepIntegral.vacuumNormalization =
      vacuumNormalization dataSet
  ; P3.ExactOneStepIntegral.addScalar = add (sumData dataSet)
  ; P3.ExactOneStepIntegral.multiplyScalar = multiply dataSet
  ; P3.ExactOneStepIntegral.smallLargePartitionExact =
      smallLargePartitionExact (sumData dataSet)
  ; P3.ExactOneStepIntegral.effectiveActionDefinesIntegral =
      effectiveActionDefinesIntegral dataSet
  }

p3FiniteConstrainedSumDefinitionLevel : ProofLevel
p3FiniteConstrainedSumDefinitionLevel = machineChecked

p3FiniteSmallLargePartitionLevel : ProofLevel
p3FiniteSmallLargePartitionLevel = machineChecked

p3FiniteEffectiveActionAdapterLevel : ProofLevel
p3FiniteEffectiveActionAdapterLevel = machineChecked

-- Passing from exact finite quadrature to the compact SU(N) product Haar measure,
-- and controlling that limit uniformly, remains part of the physical producer.
p3CompactHaarIntegralLimitLevel : ProofLevel
p3CompactHaarIntegralLimitLevel = conditional
