module DASHI.Physics.YangMills.BalabanBishopSetoidAlternatingFirstOmittedExact where

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
-- The alternating first-omitted theorem must respect Bishop setoid equality.
-- This module proves the signed tail inequalities from even/odd partial-sum
-- brackets and instantiates every order operation on the actual Bishop reals.
-- The remaining analytic input is precisely the order-closed bracketing of the
-- represented sine/cosine limit by its concrete partial sums.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal
import RealProperties as BishopProperties

open import DASHI.Physics.YangMills.CompactLieProofLevel

record SetoidOrderedDifferenceKernel (Scalar : Set) : Set₁ where
  field
    zero : Scalar
    subtract : Scalar → Scalar → Scalar

    Equivalent : Scalar → Scalar → Set
    LessEqual : Scalar → Scalar → Set

    differenceNonnegative :
      ∀ {lower upper} →
      LessEqual lower upper →
      LessEqual zero (subtract upper lower)

    subtractRightMonotone :
      ∀ {left upper common} →
      LessEqual left upper →
      LessEqual
        (subtract left common)
        (subtract upper common)

    subtractLeftAntitone :
      ∀ {lower upper common} →
      LessEqual lower upper →
      LessEqual
        (subtract common upper)
        (subtract common lower)

    lessEqualRespectRight :
      ∀ {left upper target} →
      Equivalent upper target →
      LessEqual left upper →
      LessEqual left target

open SetoidOrderedDifferenceKernel public

record SetoidAlternatingPartialSumBrackets
    {Scalar : Set}
    (kernel : SetoidOrderedDifferenceKernel Scalar) : Set₁ where
  field
    lowerPartial : Nat → Scalar
    upperPartial : Nat → Scalar
    nextLowerPartial : Nat → Scalar
    limit : Scalar

    firstOmittedAfterLower : Nat → Scalar
    firstOmittedAfterUpper : Nat → Scalar

    lowerBelowLimit :
      ∀ index →
      LessEqual kernel (lowerPartial index) limit

    limitBelowUpper :
      ∀ index →
      LessEqual kernel limit (upperPartial index)

    nextLowerBelowLimit :
      ∀ index →
      LessEqual kernel (nextLowerPartial index) limit

    upperMinusLowerEquivalentFirstOmitted :
      ∀ index →
      Equivalent kernel
        (subtract kernel (upperPartial index) (lowerPartial index))
        (firstOmittedAfterLower index)

    upperMinusNextLowerEquivalentFirstOmitted :
      ∀ index →
      Equivalent kernel
        (subtract kernel (upperPartial index) (nextLowerPartial index))
        (firstOmittedAfterUpper index)

open SetoidAlternatingPartialSumBrackets public

record SetoidSignedFirstOmittedTail
    {Scalar : Set}
    (kernel : SetoidOrderedDifferenceKernel Scalar) : Set₁ where
  field
    brackets : SetoidAlternatingPartialSumBrackets kernel

    lowerTailNonnegative :
      ∀ index →
      LessEqual kernel
        (zero kernel)
        (subtract kernel
          (SetoidAlternatingPartialSumBrackets.limit brackets)
          (SetoidAlternatingPartialSumBrackets.lowerPartial brackets index))

    lowerTailBelowFirstOmitted :
      ∀ index →
      LessEqual kernel
        (subtract kernel
          (SetoidAlternatingPartialSumBrackets.limit brackets)
          (SetoidAlternatingPartialSumBrackets.lowerPartial brackets index))
        (SetoidAlternatingPartialSumBrackets.firstOmittedAfterLower
          brackets index)

    upperTailNonnegative :
      ∀ index →
      LessEqual kernel
        (zero kernel)
        (subtract kernel
          (SetoidAlternatingPartialSumBrackets.upperPartial brackets index)
          (SetoidAlternatingPartialSumBrackets.limit brackets))

    upperTailBelowFirstOmitted :
      ∀ index →
      LessEqual kernel
        (subtract kernel
          (SetoidAlternatingPartialSumBrackets.upperPartial brackets index)
          (SetoidAlternatingPartialSumBrackets.limit brackets))
        (SetoidAlternatingPartialSumBrackets.firstOmittedAfterUpper
          brackets index)

open SetoidSignedFirstOmittedTail public

setoidLowerTailBelowFirstOmitted :
  ∀ {Scalar : Set}
    {kernel : SetoidOrderedDifferenceKernel Scalar} →
  (brackets : SetoidAlternatingPartialSumBrackets kernel) →
  ∀ index →
  LessEqual kernel
    (subtract kernel
      (SetoidAlternatingPartialSumBrackets.limit brackets)
      (SetoidAlternatingPartialSumBrackets.lowerPartial brackets index))
    (SetoidAlternatingPartialSumBrackets.firstOmittedAfterLower
      brackets index)
setoidLowerTailBelowFirstOmitted {kernel = kernel} brackets index =
  SetoidOrderedDifferenceKernel.lessEqualRespectRight kernel
    (SetoidAlternatingPartialSumBrackets.upperMinusLowerEquivalentFirstOmitted
      brackets index)
    (SetoidOrderedDifferenceKernel.subtractRightMonotone kernel
      (SetoidAlternatingPartialSumBrackets.limitBelowUpper brackets index))

setoidUpperTailBelowFirstOmitted :
  ∀ {Scalar : Set}
    {kernel : SetoidOrderedDifferenceKernel Scalar} →
  (brackets : SetoidAlternatingPartialSumBrackets kernel) →
  ∀ index →
  LessEqual kernel
    (subtract kernel
      (SetoidAlternatingPartialSumBrackets.upperPartial brackets index)
      (SetoidAlternatingPartialSumBrackets.limit brackets))
    (SetoidAlternatingPartialSumBrackets.firstOmittedAfterUpper
      brackets index)
setoidUpperTailBelowFirstOmitted {kernel = kernel} brackets index =
  SetoidOrderedDifferenceKernel.lessEqualRespectRight kernel
    (SetoidAlternatingPartialSumBrackets.upperMinusNextLowerEquivalentFirstOmitted
      brackets index)
    (SetoidOrderedDifferenceKernel.subtractLeftAntitone kernel
      (SetoidAlternatingPartialSumBrackets.nextLowerBelowLimit brackets index))

setoidAlternatingBracketsGiveFirstOmittedTail :
  ∀ {Scalar : Set}
    {kernel : SetoidOrderedDifferenceKernel Scalar} →
  (brackets : SetoidAlternatingPartialSumBrackets kernel) →
  SetoidSignedFirstOmittedTail kernel
setoidAlternatingBracketsGiveFirstOmittedTail
  {kernel = kernel} brackets = record
  { brackets = brackets
  ; lowerTailNonnegative = λ index →
      SetoidOrderedDifferenceKernel.differenceNonnegative kernel
        (SetoidAlternatingPartialSumBrackets.lowerBelowLimit brackets index)
  ; lowerTailBelowFirstOmitted =
      setoidLowerTailBelowFirstOmitted brackets
  ; upperTailNonnegative = λ index →
      SetoidOrderedDifferenceKernel.differenceNonnegative kernel
        (SetoidAlternatingPartialSumBrackets.limitBelowUpper brackets index)
  ; upperTailBelowFirstOmitted =
      setoidUpperTailBelowFirstOmitted brackets
  }

bishopSetoidOrderedDifferenceKernel :
  SetoidOrderedDifferenceKernel BishopReal.ℝ
bishopSetoidOrderedDifferenceKernel = record
  { zero = BishopReal.0ℝ
  ; subtract = BishopReal._-_
  ; Equivalent = BishopReal._≃_
  ; LessEqual = BishopReal._≤_
  ; differenceNonnegative = BishopProperties.nonNegx⇒0≤x
  ; subtractRightMonotone = λ bound →
      BishopProperties.+-monoˡ-≤ _ bound
  ; subtractLeftAntitone = λ bound →
      BishopProperties.+-monoʳ-≤ _
        (BishopProperties.neg-mono-≤ bound)
  ; lessEqualRespectRight = BishopProperties.≤-respʳ-≃
  }

bishopAlternatingBracketsGiveFirstOmittedTail :
  (brackets :
    SetoidAlternatingPartialSumBrackets
      bishopSetoidOrderedDifferenceKernel) →
  SetoidSignedFirstOmittedTail
    bishopSetoidOrderedDifferenceKernel
bishopAlternatingBracketsGiveFirstOmittedTail =
  setoidAlternatingBracketsGiveFirstOmittedTail

bishopSetoidAlternatingTailLevel : ProofLevel
bishopSetoidAlternatingTailLevel = machineChecked

bishopOrderClosedPartialSumBracketLevel : ProofLevel
bishopOrderClosedPartialSumBracketLevel = conditional
