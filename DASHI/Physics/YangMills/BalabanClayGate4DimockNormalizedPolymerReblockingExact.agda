module DASHI.Physics.YangMills.BalabanClayGate4DimockNormalizedPolymerReblockingExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact algebra behind Dimock I, Lemmas 10--11.
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban - I. Small Fields",
-- arXiv:1108.1335v2 [math-ph]. No DOI recorded.
--
-- The source first obtains a raw reblocking loss of order 9 K0 L^3 and then
-- removes relevant Taylor coefficients on small polymers.  The normalized
-- contribution gains enough powers of L to produce an O(1)L^{-epsilon}
-- contraction.  The theorem below separates these two estimates and derives
-- the composed contraction; consumers cannot silently assume the final bound
-- independently of raw reblocking and normalization.
------------------------------------------------------------------------

record OrderedNormProduct (Scalar : Set) : Set₁ where
  field
    multiply : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    multiplyMonotone : ∀ {left lower right upper} →
      LessEqual left lower → LessEqual right upper →
      LessEqual (multiply left right) (multiply lower upper)

    multiplyAssociative : ∀ left middle right →
      multiply (multiply left middle) right
      ≡ multiply left (multiply middle right)

open OrderedNormProduct public

record NormalizedPolymerReblockingData (Scalar : Set) : Set₁ where
  field
    algebra : OrderedNormProduct Scalar

    currentNorm rawReblockedNorm normalizedReblockedNorm : Scalar
    rawReblockingFactor normalizationGain contractionFactor : Scalar

    rawReblockingEstimate :
      LessEqual algebra rawReblockedNorm
        (multiply algebra rawReblockingFactor currentNorm)

    normalizationEstimate :
      LessEqual algebra normalizedReblockedNorm
        (multiply algebra normalizationGain rawReblockedNorm)

    contractionFactorMeaning :
      contractionFactor
      ≡ multiply algebra normalizationGain rawReblockingFactor

open NormalizedPolymerReblockingData public

normalizedReblockingBelowFactorProduct :
  ∀ {Scalar}
    (dataSet : NormalizedPolymerReblockingData Scalar) →
  LessEqual (algebra dataSet)
    (normalizedReblockedNorm dataSet)
    (multiply (algebra dataSet)
      (contractionFactor dataSet)
      (currentNorm dataSet))
normalizedReblockingBelowFactorProduct dataSet =
  subst
    (λ factor →
      LessEqual (algebra dataSet)
        (normalizedReblockedNorm dataSet)
        (multiply (algebra dataSet) factor (currentNorm dataSet)))
    (sym (contractionFactorMeaning dataSet))
    (transitive (algebra dataSet)
      (normalizationEstimate dataSet)
      (subst
        (λ upper →
          LessEqual (algebra dataSet)
            (multiply (algebra dataSet)
              (normalizationGain dataSet)
              (rawReblockedNorm dataSet))
            upper)
        (sym
          (multiplyAssociative (algebra dataSet)
            (normalizationGain dataSet)
            (rawReblockingFactor dataSet)
            (currentNorm dataSet)))
        (multiplyMonotone (algebra dataSet)
          (reflexive (algebra dataSet) (normalizationGain dataSet))
          (rawReblockingEstimate dataSet))))

record ContractiveNormalizedReblocking
    {Scalar : Set}
    (dataSet : NormalizedPolymerReblockingData Scalar) : Set₁ where
  field
    targetContraction : Scalar
    factorBelowTarget :
      LessEqual (algebra dataSet)
        (contractionFactor dataSet) targetContraction

open ContractiveNormalizedReblocking public

normalizedReblockingBelowTargetContraction :
  ∀ {Scalar}
    {dataSet : NormalizedPolymerReblockingData Scalar} →
  (certificate : ContractiveNormalizedReblocking dataSet) →
  LessEqual (algebra dataSet)
    (normalizedReblockedNorm dataSet)
    (multiply (algebra dataSet)
      (targetContraction certificate)
      (currentNorm dataSet))
normalizedReblockingBelowTargetContraction {dataSet = dataSet} certificate =
  transitive (algebra dataSet)
    (normalizedReblockingBelowFactorProduct dataSet)
    (multiplyMonotone (algebra dataSet)
      (factorBelowTarget certificate)
      (reflexive (algebra dataSet) (currentNorm dataSet)))

dimockRawReblockingCompositionLevel : ProofLevel
dimockRawReblockingCompositionLevel = machineChecked

dimockNormalizedPolymerContractionAssemblyLevel : ProofLevel
dimockNormalizedPolymerContractionAssemblyLevel = machineChecked

dimockNormalizedReblockingSourceLevel : ProofLevel
dimockNormalizedReblockingSourceLevel = standardImported

physicalYangMillsRelevantTaylorExtractionInputsLevel : ProofLevel
physicalYangMillsRelevantTaylorExtractionInputsLevel = conditional

physicalYangMillsPolymerNormScalingInputsLevel : ProofLevel
physicalYangMillsPolymerNormScalingInputsLevel = conditional
