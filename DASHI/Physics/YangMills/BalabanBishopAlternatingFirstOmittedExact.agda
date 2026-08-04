module DASHI.Physics.YangMills.BalabanBishopAlternatingFirstOmittedExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Zachary Murray, "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- The classical alternating-series remainder argument is constructive once
-- the even/odd partial sums bracket the represented limit.  This module makes
-- that order argument explicit.  It does not import a real-valued sine or
-- cosine theorem: callers must supply the partial-sum brackets obtained from
-- the concrete coefficient recurrence, decreasing magnitudes and the
-- order-closed Bishop limit.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record OrderedDifferenceKernel (Scalar : Set) : Set₁ where
  field
    zero : Scalar
    subtract : Scalar → Scalar → Scalar
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

open OrderedDifferenceKernel public

record AlternatingPartialSumBrackets
    {Scalar : Set}
    (kernel : OrderedDifferenceKernel Scalar) : Set₁ where
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

    upperMinusLowerIsFirstOmitted :
      ∀ index →
      subtract kernel (upperPartial index) (lowerPartial index)
        ≡ firstOmittedAfterLower index

    upperMinusNextLowerIsFirstOmitted :
      ∀ index →
      subtract kernel (upperPartial index) (nextLowerPartial index)
        ≡ firstOmittedAfterUpper index

open AlternatingPartialSumBrackets public

record SignedFirstOmittedTail
    {Scalar : Set}
    (kernel : OrderedDifferenceKernel Scalar) : Set₁ where
  field
    lowerPartial : Nat → Scalar
    upperPartial : Nat → Scalar
    limit : Scalar
    firstOmittedAfterLower : Nat → Scalar
    firstOmittedAfterUpper : Nat → Scalar

    lowerTailNonnegative :
      ∀ index →
      LessEqual kernel
        (zero kernel)
        (subtract kernel limit (lowerPartial index))

    lowerTailBelowFirstOmitted :
      ∀ index →
      LessEqual kernel
        (subtract kernel limit (lowerPartial index))
        (firstOmittedAfterLower index)

    upperTailNonnegative :
      ∀ index →
      LessEqual kernel
        (zero kernel)
        (subtract kernel (upperPartial index) limit)

    upperTailBelowFirstOmitted :
      ∀ index →
      LessEqual kernel
        (subtract kernel (upperPartial index) limit)
        (firstOmittedAfterUpper index)

open SignedFirstOmittedTail public

lowerTailBound :
  ∀ {Scalar : Set}
    {kernel : OrderedDifferenceKernel Scalar} →
  (brackets : AlternatingPartialSumBrackets kernel) →
  ∀ index →
  LessEqual kernel
    (subtract kernel
      (AlternatingPartialSumBrackets.limit brackets)
      (AlternatingPartialSumBrackets.lowerPartial brackets index))
    (AlternatingPartialSumBrackets.firstOmittedAfterLower brackets index)
lowerTailBound {kernel = kernel} brackets index =
  subst
    (λ upper →
      LessEqual kernel
        (subtract kernel
          (AlternatingPartialSumBrackets.limit brackets)
          (AlternatingPartialSumBrackets.lowerPartial brackets index))
        upper)
    (AlternatingPartialSumBrackets.upperMinusLowerIsFirstOmitted
      brackets index)
    (OrderedDifferenceKernel.subtractRightMonotone kernel
      (AlternatingPartialSumBrackets.limitBelowUpper brackets index))

upperTailBound :
  ∀ {Scalar : Set}
    {kernel : OrderedDifferenceKernel Scalar} →
  (brackets : AlternatingPartialSumBrackets kernel) →
  ∀ index →
  LessEqual kernel
    (subtract kernel
      (AlternatingPartialSumBrackets.upperPartial brackets index)
      (AlternatingPartialSumBrackets.limit brackets))
    (AlternatingPartialSumBrackets.firstOmittedAfterUpper brackets index)
upperTailBound {kernel = kernel} brackets index =
  subst
    (λ upper →
      LessEqual kernel
        (subtract kernel
          (AlternatingPartialSumBrackets.upperPartial brackets index)
          (AlternatingPartialSumBrackets.limit brackets))
        upper)
    (AlternatingPartialSumBrackets.upperMinusNextLowerIsFirstOmitted
      brackets index)
    (OrderedDifferenceKernel.subtractLeftAntitone kernel
      (AlternatingPartialSumBrackets.nextLowerBelowLimit brackets index))

alternatingBracketsGiveFirstOmittedTail :
  ∀ {Scalar : Set}
    {kernel : OrderedDifferenceKernel Scalar} →
  AlternatingPartialSumBrackets kernel →
  SignedFirstOmittedTail kernel
alternatingBracketsGiveFirstOmittedTail {kernel = kernel} brackets = record
  { lowerPartial =
      AlternatingPartialSumBrackets.lowerPartial brackets
  ; upperPartial =
      AlternatingPartialSumBrackets.upperPartial brackets
  ; limit =
      AlternatingPartialSumBrackets.limit brackets
  ; firstOmittedAfterLower =
      AlternatingPartialSumBrackets.firstOmittedAfterLower brackets
  ; firstOmittedAfterUpper =
      AlternatingPartialSumBrackets.firstOmittedAfterUpper brackets
  ; lowerTailNonnegative = λ index →
      OrderedDifferenceKernel.differenceNonnegative kernel
        (AlternatingPartialSumBrackets.lowerBelowLimit brackets index)
  ; lowerTailBelowFirstOmitted =
      lowerTailBound brackets
  ; upperTailNonnegative = λ index →
      OrderedDifferenceKernel.differenceNonnegative kernel
        (AlternatingPartialSumBrackets.limitBelowUpper brackets index)
  ; upperTailBelowFirstOmitted =
      upperTailBound brackets
  }

record SineCosineAlternatingBrackets
    {Scalar : Set}
    (kernel : OrderedDifferenceKernel Scalar) : Set₁ where
  field
    sine : AlternatingPartialSumBrackets kernel
    cosine : AlternatingPartialSumBrackets kernel

open SineCosineAlternatingBrackets public

record SineCosineFirstOmittedTails
    {Scalar : Set}
    (kernel : OrderedDifferenceKernel Scalar) : Set₁ where
  field
    sine : SignedFirstOmittedTail kernel
    cosine : SignedFirstOmittedTail kernel

open SineCosineFirstOmittedTails public

sineCosineBracketsGiveFirstOmittedTails :
  ∀ {Scalar : Set}
    {kernel : OrderedDifferenceKernel Scalar} →
  SineCosineAlternatingBrackets kernel →
  SineCosineFirstOmittedTails kernel
sineCosineBracketsGiveFirstOmittedTails inputs = record
  { sine = alternatingBracketsGiveFirstOmittedTail
      (SineCosineAlternatingBrackets.sine inputs)
  ; cosine = alternatingBracketsGiveFirstOmittedTail
      (SineCosineAlternatingBrackets.cosine inputs)
  }

bishopAlternatingFirstOmittedReductionLevel : ProofLevel
bishopAlternatingFirstOmittedReductionLevel = machineChecked

bishopAlternatingPartialSumBracketInputsLevel : ProofLevel
bishopAlternatingPartialSumBracketInputsLevel = conditional
