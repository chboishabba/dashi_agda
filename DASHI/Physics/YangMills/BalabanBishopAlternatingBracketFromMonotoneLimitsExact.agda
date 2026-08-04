module DASHI.Physics.YangMills.BalabanBishopAlternatingBracketFromMonotoneLimitsExact where

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
-- Close the order-closed limit passage for alternating Bishop series.  Once
-- the lower subsequence is increasing, the upper subsequence is decreasing,
-- both converge to the represented value, and the adjacent differences are
-- the omitted magnitudes, the concrete setoid bracket record follows without
-- a further order-completeness assumption.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)

import Real as BishopReal
import RealProperties as BishopProperties
import Sequence as BishopSequence

import DASHI.Physics.YangMills.BalabanBishopSetoidAlternatingFirstOmittedExact as Alternating
import DASHI.Physics.YangMills.BalabanBishopSeriesParityAndLimitExact as ParityLimit
open import DASHI.Physics.YangMills.CompactLieProofLevel

record BishopAlternatingInterlacingData : Set₁ where
  field
    lowerPartial upperPartial nextLowerPartial :
      Nat → BishopReal.ℝ

    representedLimit : BishopReal.ℝ

    firstOmittedAfterLower firstOmittedAfterUpper :
      Nat → BishopReal.ℝ

    lowerIncreasing :
      BishopSequence._isIncreasing lowerPartial

    upperDecreasing :
      BishopSequence._isDecreasing upperPartial

    lowerConverges :
      BishopSequence._isConvergent lowerPartial

    upperConverges :
      BishopSequence._isConvergent upperPartial

    lowerLimitIsRepresentedLimit :
      BishopReal._≃_
        (BishopSequence.lim lowerConverges)
        representedLimit

    upperLimitIsRepresentedLimit :
      BishopReal._≃_
        (BishopSequence.lim upperConverges)
        representedLimit

    nextLowerIsSuccessorLower :
      ∀ index →
      BishopReal._≃_
        (nextLowerPartial index)
        (lowerPartial (suc index))

    upperMinusLowerEquivalentFirstOmitted :
      ∀ index →
      BishopReal._≃_
        (BishopReal._-_
          (upperPartial index)
          (lowerPartial index))
        (firstOmittedAfterLower index)

    upperMinusNextLowerEquivalentFirstOmitted :
      ∀ index →
      BishopReal._≃_
        (BishopReal._-_
          (upperPartial index)
          (nextLowerPartial index))
        (firstOmittedAfterUpper index)

open BishopAlternatingInterlacingData public

lowerPartialBelowRepresentedLimit :
  (dataSet : BishopAlternatingInterlacingData) →
  ∀ index →
  BishopReal._≤_
    (lowerPartial dataSet index)
    (representedLimit dataSet)
lowerPartialBelowRepresentedLimit dataSet index =
  BishopProperties.≤-respʳ-≃
    (lowerLimitIsRepresentedLimit dataSet)
    (BishopSequence.xₙisIncreasing⇒xₙ≤limxₙ
      (lowerIncreasing dataSet)
      (lowerConverges dataSet)
      index)

representedLimitBelowUpperPartial :
  (dataSet : BishopAlternatingInterlacingData) →
  ∀ index →
  BishopReal._≤_
    (representedLimit dataSet)
    (upperPartial dataSet index)
representedLimitBelowUpperPartial dataSet index =
  BishopProperties.≤-respˡ-≃
    (BishopProperties.≃-symm
      (upperLimitIsRepresentedLimit dataSet))
    (BishopSequence.xₙisDecreasing⇒limxₙ≤xₙ
      (upperDecreasing dataSet)
      (upperConverges dataSet)
      index)

nextLowerPartialBelowRepresentedLimit :
  (dataSet : BishopAlternatingInterlacingData) →
  ∀ index →
  BishopReal._≤_
    (nextLowerPartial dataSet index)
    (representedLimit dataSet)
nextLowerPartialBelowRepresentedLimit dataSet index =
  BishopProperties.≤-respˡ-≃
    (nextLowerIsSuccessorLower dataSet index)
    (lowerPartialBelowRepresentedLimit dataSet (suc index))

bishopAlternatingBracketsFromInterlacing :
  BishopAlternatingInterlacingData →
  Alternating.SetoidAlternatingPartialSumBrackets
    Alternating.bishopSetoidOrderedDifferenceKernel
bishopAlternatingBracketsFromInterlacing dataSet = record
  { lowerPartial = lowerPartial dataSet
  ; upperPartial = upperPartial dataSet
  ; nextLowerPartial = nextLowerPartial dataSet
  ; limit = representedLimit dataSet
  ; firstOmittedAfterLower = firstOmittedAfterLower dataSet
  ; firstOmittedAfterUpper = firstOmittedAfterUpper dataSet
  ; lowerBelowLimit = lowerPartialBelowRepresentedLimit dataSet
  ; limitBelowUpper = representedLimitBelowUpperPartial dataSet
  ; nextLowerBelowLimit =
      nextLowerPartialBelowRepresentedLimit dataSet
  ; upperMinusLowerEquivalentFirstOmitted =
      upperMinusLowerEquivalentFirstOmitted dataSet
  ; upperMinusNextLowerEquivalentFirstOmitted =
      upperMinusNextLowerEquivalentFirstOmitted dataSet
  }

record BishopSineCosineInterlacingData : Set₁ where
  field
    sineInterlacing : BishopAlternatingInterlacingData
    cosineInterlacing : BishopAlternatingInterlacingData

open BishopSineCosineInterlacingData public

concreteBishopAlternatingBracketsFromInterlacing :
  BishopSineCosineInterlacingData →
  ParityLimit.ConcreteBishopAlternatingBrackets
concreteBishopAlternatingBracketsFromInterlacing dataSet = record
  { sineBrackets =
      bishopAlternatingBracketsFromInterlacing
        (sineInterlacing dataSet)
  ; cosineBrackets =
      bishopAlternatingBracketsFromInterlacing
        (cosineInterlacing dataSet)
  }

bishopAlternatingOrderClosureLevel : ProofLevel
bishopAlternatingOrderClosureLevel = machineChecked

bishopAlternatingBracketAssemblyFromInterlacingLevel : ProofLevel
bishopAlternatingBracketAssemblyFromInterlacingLevel = machineChecked

bishopConcreteSineCosineInterlacingInputsLevel : ProofLevel
bishopConcreteSineCosineInterlacingInputsLevel = conditional
