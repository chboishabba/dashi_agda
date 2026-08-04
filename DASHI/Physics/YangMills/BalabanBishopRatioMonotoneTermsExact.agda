module DASHI.Physics.YangMills.BalabanBishopRatioMonotoneTermsExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Zachary Murray, "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- PURPOSE
--
-- The half-radius sine/cosine lane already owns the exact rational ratios
--
--   sine   <= 1/24,
--   cosine <= 1/8.
--
-- This module closes the order-theoretic step from a nonnegative successive
-- coefficient recurrence and a subunit ratio to monotonicity of term
-- magnitudes.  The proof is generic so it can be instantiated directly by the
-- Bishop real backend without introducing a second elementary-function axiom.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record OrderedRatioKernel (Scalar : Set) : Set₁ where
  field
    one : Scalar
    multiply : Scalar → Scalar → Scalar

    Nonnegative : Scalar → Set
    LessEqual : Scalar → Scalar → Set

    multiplyRightMonotone :
      ∀ {left upper right} →
      Nonnegative right →
      LessEqual left upper →
      LessEqual (multiply left right) (multiply upper right)

    oneLeftIdentity :
      ∀ value → multiply one value ≡ value

open OrderedRatioKernel public

record SuccessiveRatioTerms
    {Scalar : Set}
    (kernel : OrderedRatioKernel Scalar) : Set₁ where
  field
    term ratio : Nat → Scalar

    recurrence :
      ∀ index →
      term (suc index)
        ≡ multiply kernel (ratio index) (term index)

    termNonnegative :
      ∀ index → Nonnegative kernel (term index)

    ratioBelowOne :
      ∀ index → LessEqual kernel (ratio index) (one kernel)

open SuccessiveRatioTerms public

record DecreasingMagnitudeTerms
    {Scalar : Set}
    (kernel : OrderedRatioKernel Scalar) : Set₁ where
  field
    term : Nat → Scalar
    successorBelowCurrent :
      ∀ index →
      LessEqual kernel (term (suc index)) (term index)

open DecreasingMagnitudeTerms public

successiveRatioGivesDecreasing :
  ∀ {Scalar : Set}
    {kernel : OrderedRatioKernel Scalar} →
  (dataSet : SuccessiveRatioTerms kernel) →
  ∀ index →
  LessEqual kernel
    (SuccessiveRatioTerms.term dataSet (suc index))
    (SuccessiveRatioTerms.term dataSet index)
successiveRatioGivesDecreasing {kernel = kernel} dataSet index =
  let current = SuccessiveRatioTerms.term dataSet index
      currentNonnegative =
        SuccessiveRatioTerms.termNonnegative dataSet index
      ratioBound =
        SuccessiveRatioTerms.ratioBelowOne dataSet index
      productBound =
        OrderedRatioKernel.multiplyRightMonotone kernel
          currentNonnegative
          ratioBound
      productToCurrent =
        subst
          (λ upper →
            OrderedRatioKernel.LessEqual kernel
              (OrderedRatioKernel.multiply kernel
                (SuccessiveRatioTerms.ratio dataSet index)
                current)
              upper)
          (OrderedRatioKernel.oneLeftIdentity kernel current)
          productBound
  in subst
       (λ lower →
         OrderedRatioKernel.LessEqual kernel lower current)
       (sym (SuccessiveRatioTerms.recurrence dataSet index))
       productToCurrent

successiveRatioTermsToDecreasing :
  ∀ {Scalar : Set}
    {kernel : OrderedRatioKernel Scalar} →
  SuccessiveRatioTerms kernel →
  DecreasingMagnitudeTerms kernel
successiveRatioTermsToDecreasing dataSet = record
  { term = SuccessiveRatioTerms.term dataSet
  ; successorBelowCurrent =
      successiveRatioGivesDecreasing dataSet
  }

record HalfRadiusSineCosineRatioTerms
    {Scalar : Set}
    (kernel : OrderedRatioKernel Scalar) : Set₁ where
  field
    sine : SuccessiveRatioTerms kernel
    cosine : SuccessiveRatioTerms kernel

open HalfRadiusSineCosineRatioTerms public

record HalfRadiusSineCosineDecreasingTerms
    {Scalar : Set}
    (kernel : OrderedRatioKernel Scalar) : Set₁ where
  field
    sine : DecreasingMagnitudeTerms kernel
    cosine : DecreasingMagnitudeTerms kernel

open HalfRadiusSineCosineDecreasingTerms public

halfRadiusRatioTermsGiveDecreasingTerms :
  ∀ {Scalar : Set}
    {kernel : OrderedRatioKernel Scalar} →
  HalfRadiusSineCosineRatioTerms kernel →
  HalfRadiusSineCosineDecreasingTerms kernel
halfRadiusRatioTermsGiveDecreasingTerms inputs = record
  { sine = successiveRatioTermsToDecreasing
      (HalfRadiusSineCosineRatioTerms.sine inputs)
  ; cosine = successiveRatioTermsToDecreasing
      (HalfRadiusSineCosineRatioTerms.cosine inputs)
  }

bishopRatioToMonotoneTermsLevel : ProofLevel
bishopRatioToMonotoneTermsLevel = machineChecked

bishopConcreteCoefficientRecurrenceInputsLevel : ProofLevel
bishopConcreteCoefficientRecurrenceInputsLevel = conditional
