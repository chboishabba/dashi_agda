module DASHI.Physics.YangMills.BalabanBishopSetoidRatioMonotoneExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Zachary Murray, "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- Code continuation: Viktor Csimma, viktorcsimma/bishop, pinned by DASHI at
-- vendor/bishop commit 240e38c7f6938f20f865b1f956c5f084da48bd54.
--
-- PURPOSE
--
-- The concrete Bishop carrier uses setoid equality.  This module proves the
-- ratio-to-decreasing-term step with setoid transport and then supplies the
-- actual Bishop ordered-ratio kernel.  Only the concrete sine/cosine
-- coefficient recurrence remains to be supplied by the term definitions.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)

import Real as BishopReal
import RealProperties as BishopProperties

open import DASHI.Physics.YangMills.CompactLieProofLevel

record SetoidOrderedRatioKernel (Scalar : Set) : Set₁ where
  field
    one : Scalar
    multiply : Scalar → Scalar → Scalar

    Equivalent : Scalar → Scalar → Set
    Nonnegative : Scalar → Set
    LessEqual : Scalar → Scalar → Set

    equivalentSymmetric :
      ∀ {left right} →
      Equivalent left right → Equivalent right left

    multiplyRightMonotone :
      ∀ {left upper right} →
      Nonnegative right →
      LessEqual left upper →
      LessEqual (multiply left right) (multiply upper right)

    lessEqualRespectRight :
      ∀ {left upper target} →
      Equivalent upper target →
      LessEqual left upper →
      LessEqual left target

    lessEqualRespectLeft :
      ∀ {left target right} →
      Equivalent left target →
      LessEqual left right →
      LessEqual target right

    oneLeftIdentity :
      ∀ value → Equivalent (multiply one value) value

open SetoidOrderedRatioKernel public

record SetoidSuccessiveRatioTerms
    {Scalar : Set}
    (kernel : SetoidOrderedRatioKernel Scalar) : Set₁ where
  field
    term ratio : Nat → Scalar

    recurrence :
      ∀ index →
      Equivalent kernel
        (term (suc index))
        (multiply kernel (ratio index) (term index))

    termNonnegative :
      ∀ index → Nonnegative kernel (term index)

    ratioBelowOne :
      ∀ index → LessEqual kernel (ratio index) (one kernel)

open SetoidSuccessiveRatioTerms public

setoidSuccessiveRatioGivesDecreasing :
  ∀ {Scalar : Set}
    {kernel : SetoidOrderedRatioKernel Scalar} →
  (dataSet : SetoidSuccessiveRatioTerms kernel) →
  ∀ index →
  LessEqual kernel
    (SetoidSuccessiveRatioTerms.term dataSet (suc index))
    (SetoidSuccessiveRatioTerms.term dataSet index)
setoidSuccessiveRatioGivesDecreasing {kernel = kernel} dataSet index =
  let current = SetoidSuccessiveRatioTerms.term dataSet index
      productBound =
        SetoidOrderedRatioKernel.multiplyRightMonotone kernel
          (SetoidSuccessiveRatioTerms.termNonnegative dataSet index)
          (SetoidSuccessiveRatioTerms.ratioBelowOne dataSet index)
      productToCurrent =
        SetoidOrderedRatioKernel.lessEqualRespectRight kernel
          (SetoidOrderedRatioKernel.oneLeftIdentity kernel current)
          productBound
      productEquivalentSuccessor =
        SetoidOrderedRatioKernel.equivalentSymmetric kernel
          (SetoidSuccessiveRatioTerms.recurrence dataSet index)
  in SetoidOrderedRatioKernel.lessEqualRespectLeft kernel
       productEquivalentSuccessor
       productToCurrent

bishopSetoidOrderedRatioKernel :
  SetoidOrderedRatioKernel BishopReal.ℝ
bishopSetoidOrderedRatioKernel = record
  { one = BishopReal.1ℝ
  ; multiply = BishopReal._*_
  ; Equivalent = BishopReal._≃_
  ; Nonnegative = BishopReal.NonNegative
  ; LessEqual = BishopReal._≤_
  ; equivalentSymmetric = BishopProperties.≃-symm
  ; multiplyRightMonotone = λ nonnegative bound →
      BishopProperties.*-monoʳ-≤-nonNeg bound nonnegative
  ; lessEqualRespectRight = BishopProperties.≤-respʳ-≃
  ; lessEqualRespectLeft = BishopProperties.≤-respˡ-≃
  ; oneLeftIdentity = BishopProperties.*-identityˡ
  }

bishopSuccessiveRatioGivesDecreasing :
  (dataSet : SetoidSuccessiveRatioTerms bishopSetoidOrderedRatioKernel) →
  ∀ index →
  BishopReal._≤_
    (SetoidSuccessiveRatioTerms.term dataSet (suc index))
    (SetoidSuccessiveRatioTerms.term dataSet index)
bishopSuccessiveRatioGivesDecreasing =
  setoidSuccessiveRatioGivesDecreasing

bishopSetoidRatioMonotoneLevel : ProofLevel
bishopSetoidRatioMonotoneLevel = machineChecked

bishopConcreteCoefficientRecurrenceLevel : ProofLevel
bishopConcreteCoefficientRecurrenceLevel = conditional
