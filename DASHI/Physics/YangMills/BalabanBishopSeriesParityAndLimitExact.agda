module DASHI.Physics.YangMills.BalabanBishopSeriesParityAndLimitExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- Code continuation: Viktor Csimma, viktorcsimma/bishop, pinned by DASHI at
-- vendor/bishop commit 240e38c7f6938f20f865b1f956c5f084da48bd54.
--
-- PURPOSE
-- Separate three layers which had previously been conflated:
--
--   term parity -> finite partial-sum parity;
--   convergence plus order closure -> concrete alternating brackets;
--   convergence of the transformed series plus uniqueness -> parity of the
--   represented sine/cosine limit.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)

import Real as BishopReal
import RealProperties as BishopProperties
import Sequence as BishopSequence

import DASHI.Foundations.BishopConstructiveRealBridgeExact as Bishop
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Physics.YangMills.PhysicalInvolutionParityExact as Parity
import DASHI.Physics.YangMills.BalabanBishopSetoidAlternatingFirstOmittedExact as Alternating
open import DASHI.Physics.YangMills.CompactLieProofLevel

bishopParityCodomain : Parity.ParityCodomain BishopReal.ℝ
bishopParityCodomain = record
  { Equivalent = BishopReal._≃_
  ; equivalentRefl = λ value →
      BishopProperties.≃-refl
  ; equivalentSym = BishopProperties.≃-symm
  ; equivalentTrans = BishopProperties.≃-trans
  ; zero = BishopReal.0ℝ
  ; add = BishopReal._+_
  ; negate = BishopReal.-_
  ; addCongruent = BishopProperties.+-cong
  ; addInverseRight = BishopProperties.+-inverseʳ
  ; addInverseLeft = BishopProperties.+-inverseˡ
  ; negateCongruent = BishopProperties.-‿cong
  }

bishopNegationInvolution : Parity.SetoidInvolution BishopReal.ℝ
bishopNegationInvolution = record
  { Equivalent = BishopReal._≃_
  ; equivalentRefl = λ value →
      BishopProperties.≃-refl
  ; equivalentSym = BishopProperties.≃-symm
  ; equivalentTrans = BishopProperties.≃-trans
  ; reverse = BishopReal.-_
  ; reverseCongruent = BishopProperties.-‿cong
  ; reverseInvolutive =
      BishopProperties.neg-involutive
  }

partialSum :
  (Nat → BishopReal.ℝ) → Nat → BishopReal.ℝ
partialSum term zero = BishopReal.0ℝ
partialSum term (suc count) =
  BishopReal._+_ (partialSum term count) (term count)

record BishopOddTermFamily
    (term : BishopReal.ℝ → Nat → BishopReal.ℝ) : Set₁ where
  field
    termCongruent : ∀ {left right} →
      BishopReal._≃_ left right →
      ∀ index → BishopReal._≃_ (term left index) (term right index)

    termOdd : ∀ point index →
      BishopReal._≃_
        (term (BishopReal.- point) index)
        (BishopReal.- (term point index))

open BishopOddTermFamily public

record BishopEvenTermFamily
    (term : BishopReal.ℝ → Nat → BishopReal.ℝ) : Set₁ where
  field
    termCongruent : ∀ {left right} →
      BishopReal._≃_ left right →
      ∀ index → BishopReal._≃_ (term left index) (term right index)

    termEven : ∀ point index →
      BishopReal._≃_
        (term (BishopReal.- point) index)
        (term point index)

open BishopEvenTermFamily public

oddPartialSumNegation :
  ∀ {term : BishopReal.ℝ → Nat → BishopReal.ℝ} →
  BishopOddTermFamily term →
  ∀ point count →
  BishopReal._≃_
    (partialSum (term (BishopReal.- point)) count)
    (BishopReal.- (partialSum (term point) count))
oddPartialSumNegation family point zero =
  BishopProperties.0≃-0
oddPartialSumNegation {term = term} family point (suc count) =
  BishopProperties.≃-trans
    (BishopProperties.+-cong
      (oddPartialSumNegation family point count)
      (termOdd family point count))
    (BishopProperties.≃-symm
      (BishopProperties.neg-distrib-+
        (partialSum (term point) count)
        (term point count)))

evenPartialSumNegation :
  ∀ {term : BishopReal.ℝ → Nat → BishopReal.ℝ} →
  BishopEvenTermFamily term →
  ∀ point count →
  BishopReal._≃_
    (partialSum (term (BishopReal.- point)) count)
    (partialSum (term point) count)
evenPartialSumNegation family point zero = BishopProperties.≃-refl
evenPartialSumNegation {term = term} family point (suc count) =
  BishopProperties.+-cong
    (evenPartialSumNegation family point count)
    (termEven family point count)

record BishopSeriesLimitParityInputs
    (dataSet : Elementary.BishopElementaryPowerSeriesData) : Set₁ where
  field
    sineTermsOdd :
      BishopOddTermFamily (Elementary.sineTerm dataSet)

    cosineTermsEven :
      BishopEvenTermFamily (Elementary.cosineTerm dataSet)

    sineSeriesAtNegConvergesToNegatedValue :
      ∀ point →
      Bishop.BishopConvergesTo
        (BishopSequence.SeriesOf
          (Elementary.sineTerm dataSet (BishopReal.- point)))
        (BishopReal.- (Elementary.bishopSin dataSet point))

    cosineSeriesAtNegConvergesToSameValue :
      ∀ point →
      Bishop.BishopConvergesTo
        (BishopSequence.SeriesOf
          (Elementary.cosineTerm dataSet (BishopReal.- point)))
        (Elementary.bishopCos dataSet point)

open BishopSeriesLimitParityInputs public

bishopSinNeg :
  ∀ {dataSet : Elementary.BishopElementaryPowerSeriesData} →
  BishopSeriesLimitParityInputs dataSet →
  ∀ point →
  BishopReal._≃_
    (Elementary.bishopSin dataSet (BishopReal.- point))
    (BishopReal.- (Elementary.bishopSin dataSet point))
bishopSinNeg {dataSet = dataSet} inputs point =
  Elementary.seriesValueUnique
    (Elementary.sineSeries dataSet (BishopReal.- point))
    (sineSeriesAtNegConvergesToNegatedValue inputs point)

bishopCosNeg :
  ∀ {dataSet : Elementary.BishopElementaryPowerSeriesData} →
  BishopSeriesLimitParityInputs dataSet →
  ∀ point →
  BishopReal._≃_
    (Elementary.bishopCos dataSet (BishopReal.- point))
    (Elementary.bishopCos dataSet point)
bishopCosNeg {dataSet = dataSet} inputs point =
  Elementary.seriesValueUnique
    (Elementary.cosineSeries dataSet (BishopReal.- point))
    (cosineSeriesAtNegConvergesToSameValue inputs point)

record OrderClosedSequenceKernel (Scalar : Set) : Set₁ where
  field
    Sequence : Set
    sequenceAt : Sequence → Nat → Scalar
    ConvergesTo : Sequence → Scalar → Set
    LessEqual : Scalar → Scalar → Set

    upperBoundClosedUnderLimit :
      ∀ {sequence limit upper} →
      ConvergesTo sequence limit →
      (∀ index → LessEqual (sequenceAt sequence index) upper) →
      LessEqual limit upper

    lowerBoundClosedUnderLimit :
      ∀ {sequence limit lower} →
      ConvergesTo sequence limit →
      (∀ index → LessEqual lower (sequenceAt sequence index)) →
      LessEqual lower limit

open OrderClosedSequenceKernel public

limitPreservesUpperBound :
  ∀ {Scalar}
    {kernel : OrderClosedSequenceKernel Scalar}
    {sequence limit upper} →
  ConvergesTo kernel sequence limit →
  (∀ index → LessEqual kernel (sequenceAt kernel sequence index) upper) →
  LessEqual kernel limit upper
limitPreservesUpperBound {kernel = kernel} =
  upperBoundClosedUnderLimit kernel

limitPreservesLowerBound :
  ∀ {Scalar}
    {kernel : OrderClosedSequenceKernel Scalar}
    {sequence limit lower} →
  ConvergesTo kernel sequence limit →
  (∀ index → LessEqual kernel lower (sequenceAt kernel sequence index)) →
  LessEqual kernel lower limit
limitPreservesLowerBound {kernel = kernel} =
  lowerBoundClosedUnderLimit kernel

record ConcreteBishopAlternatingBrackets : Set₁ where
  field
    sineBrackets :
      Alternating.SetoidAlternatingPartialSumBrackets
        Alternating.bishopSetoidOrderedDifferenceKernel

    cosineBrackets :
      Alternating.SetoidAlternatingPartialSumBrackets
        Alternating.bishopSetoidOrderedDifferenceKernel

open ConcreteBishopAlternatingBrackets public

concreteSineFirstOmittedTail :
  ConcreteBishopAlternatingBrackets →
  Alternating.SetoidSignedFirstOmittedTail
    Alternating.bishopSetoidOrderedDifferenceKernel
concreteSineFirstOmittedTail brackets =
  Alternating.bishopAlternatingBracketsGiveFirstOmittedTail
    (sineBrackets brackets)

concreteCosineFirstOmittedTail :
  ConcreteBishopAlternatingBrackets →
  Alternating.SetoidSignedFirstOmittedTail
    Alternating.bishopSetoidOrderedDifferenceKernel
concreteCosineFirstOmittedTail brackets =
  Alternating.bishopAlternatingBracketsGiveFirstOmittedTail
    (cosineBrackets brackets)

bishopPartialSumParityLevel : ProofLevel
bishopPartialSumParityLevel = machineChecked

bishopRepresentedLimitParityReducerLevel : ProofLevel
bishopRepresentedLimitParityReducerLevel = machineChecked

bishopOrderClosedLimitReducerLevel : ProofLevel
bishopOrderClosedLimitReducerLevel = machineChecked

bishopConcreteTransformedConvergenceLevel : ProofLevel
bishopConcreteTransformedConvergenceLevel = conditional

bishopConcreteAlternatingBracketsLevel : ProofLevel
bishopConcreteAlternatingBracketsLevel = conditional
