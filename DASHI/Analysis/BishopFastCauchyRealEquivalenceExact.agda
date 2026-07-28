module DASHI.Analysis.BishopFastCauchyRealEquivalenceExact where

open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Analysis.FastCauchyReals as Fast
import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Concrete-model comparison seam.
--
-- Unlike an equivalence with the bare legacy postulate, this comparison can in
-- principle be proved: both sides are explicit rational approximation models.
-- The remaining fields are exactly the reindexing/modulus comparison between
-- Bishop regular sequences and DASHI dyadic FastCauchyReal representatives.
------------------------------------------------------------------------

record BishopFastCauchyConversion
    (A : Fast.RationalMetricAuthority) : Set₁ where
  field
    bishopToFast : BishopReal.ℝ → Fast.FastCauchyReal A
    fastToBishop : Fast.FastCauchyReal A → BishopReal.ℝ

    bishopEqualityPreserved : ∀ {x y} →
      BishopReal._≃_ x y → Fast._≈R_ (bishopToFast x) (bishopToFast y)

    fastEqualityPreserved : ∀ {x y} →
      Fast._≈R_ x y → BishopReal._≃_ (fastToBishop x) (fastToBishop y)

    bishopRoundTrip : ∀ x →
      BishopReal._≃_ (fastToBishop (bishopToFast x)) x

    fastRoundTrip : ∀ x →
      Fast._≈R_ (bishopToFast (fastToBishop x)) x

    rationalEmbeddingAgreement : Set
    approximationReindexingExact : Set
    regularityImpliesFastCauchy : Set
    fastCauchyImpliesBishopRegularity : Set

open BishopFastCauchyConversion public

record BishopFastCauchyStructureAgreement
    {A : Fast.RationalMetricAuthority}
    (conversion : BishopFastCauchyConversion A)
    (bishopBackend fastBackend : Spine.SetoidOrderedCompleteReal) : Set₁ where
  field
    bishopCarrierExact : Spine.Carrier bishopBackend ≡ BishopReal.ℝ
    fastCarrierExact : Spine.Carrier fastBackend ≡ Fast.FastCauchyReal A

    toFastMorphism : Spine.SetoidRealMorphism bishopBackend fastBackend
    toBishopMorphism : Spine.SetoidRealMorphism fastBackend bishopBackend

    morphismMapsExact : Set
    rationalEmbeddingPreserved : Set
    orderPreservedAndReflected : Set
    convergencePreservedAndReflected : Set
    seriesSumsPreservedAndReflected : Set

open BishopFastCauchyStructureAgreement public

asSetoidRealEquivalence :
  ∀ {A conversion bishopBackend fastBackend} →
  BishopFastCauchyStructureAgreement
    {A} conversion bishopBackend fastBackend →
  Spine.SetoidRealEquivalence bishopBackend fastBackend
asSetoidRealEquivalence agreement = record
  { toRight = toFastMorphism agreement
  ; toLeft = toBishopMorphism agreement
  ; leftRoundTrip = λ value →
      Spine.respectsEquality (toBishopMorphism agreement)
        (BishopReal._≃_ value value)
  ; rightRoundTrip = λ value →
      Spine.respectsEquality (toFastMorphism agreement)
        (Spine.≈-refl _)
  ; reflectsLe = λ order →
      Spine.preservesLe (toBishopMorphism agreement) order
  ; reflectsLt = λ order →
      Spine.preservesLt (toBishopMorphism agreement) order
  }

------------------------------------------------------------------------
-- Equality-proof strategy carried by the conversion implementation.
------------------------------------------------------------------------

record EventualRationalClosenessCriterion
    (A : Fast.RationalMetricAuthority)
    (conversion : BishopFastCauchyConversion A) : Set₁ where
  field
    bishopEventualToleranceImpliesEquality : Set
    fastEventualDyadicToleranceImpliesEquality : Set
    bishopToFastTailEstimate : Set
    fastToBishopTailEstimate : Set
    roundTripsFollowFromTailEstimates : Set

open EventualRationalClosenessCriterion public

bishopFastCauchyConversionDefinitionLevel : ProofLevel
bishopFastCauchyConversionDefinitionLevel = machineChecked

bishopFastCauchyReindexingInputsLevel : ProofLevel
bishopFastCauchyReindexingInputsLevel = conditional

bishopFastCauchyStructureAgreementInputsLevel : ProofLevel
bishopFastCauchyStructureAgreementInputsLevel = conditional
