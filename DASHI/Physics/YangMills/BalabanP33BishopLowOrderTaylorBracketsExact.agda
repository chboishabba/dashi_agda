module DASHI.Physics.YangMills.BalabanP33BishopLowOrderTaylorBracketsExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- Code continuation: Viktor Csimma, `viktorcsimma/bishop`, pinned by DASHI.
--
-- DASHI CONTRIBUTION
--
-- Extract the low-order Taylor inequalities required by the P33 SU(2)
-- functional calculus from the repository's already proved concrete
-- alternating-series interlacing.  For a nonnegative point in the half ball,
-- let
--
--   s0 = |x| / 1!,       s1 = |x^3| / 3!,
--   c0 = 1 / 0!,         c1 = |x^2| / 2!.
--
-- The concrete Bishop series satisfy
--
--   s0 - s1 <= sin(x) <= s0,
--   c0 - c1 <= cos(x) <= c0.
--
-- These are not postulated Taylor remainders: they are the index-one lower and
-- index-zero upper partial sums of the machine-checked alternating interlacing
-- theorem.  The first-omitted tail record additionally proves both signed
-- remainder bounds by the next concrete factorial terms.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (zero; suc)
open import Data.Rational.Unnormalised using (0ℚᵘ)

import Real as BishopReal
import RealProperties as BishopProperties

import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineInterlacingExact as Concrete
import DASHI.Physics.YangMills.BalabanBishopFactorialPowerRecurrenceExact as Recurrence
import DASHI.Physics.YangMills.BalabanBishopAlternatingInterlacingFromDecreasingTermsExact as Alternating
import DASHI.Physics.YangMills.BalabanBishopAlternatingBracketFromMonotoneLimitsExact as Interlacing
import DASHI.Physics.YangMills.BalabanBishopSetoidAlternatingFirstOmittedExact as FirstOmitted
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact low partial-sum identities in concrete factorial magnitudes.
------------------------------------------------------------------------

lowerZeroEquivalentZero :
  (dataSet : Alternating.AlternatingDecreasingSeriesData) →
  BishopReal._≃_
    (Alternating.lowerPartial dataSet zero)
    BishopReal.0ℝ
lowerZeroEquivalentZero dataSet = BishopProperties.≃-refl

upperZeroEquivalentFirstMagnitude :
  (dataSet : Alternating.AlternatingDecreasingSeriesData) →
  BishopReal._≃_
    (Alternating.upperPartial dataSet zero)
    (Alternating.magnitude dataSet zero)
upperZeroEquivalentFirstMagnitude dataSet =
  BishopProperties.≃-trans
    (let open BishopProperties.ℝ-Solver
     in solve 1
        (λ upper → upper ⊜ upper ⊖ Κ 0ℚᵘ)
        BishopProperties.≃-refl
        (Alternating.upperPartial dataSet zero))
    (Alternating.upperMinusLowerIsEvenMagnitude dataSet zero)

lowerOneEquivalentFirstMinusSecondMagnitude :
  (dataSet : Alternating.AlternatingDecreasingSeriesData) →
  BishopReal._≃_
    (Alternating.lowerPartial dataSet (suc zero))
    (BishopReal._-_
      (Alternating.magnitude dataSet zero)
      (Alternating.magnitude dataSet (suc zero)))
lowerOneEquivalentFirstMinusSecondMagnitude dataSet =
  BishopProperties.≃-trans
    (Alternating.lowerSuccessorExpansion dataSet zero)
    (let open BishopProperties.ℝ-Solver
     in solve 2
        (λ first second →
          Κ 0ℚᵘ ⊕ (first ⊖ second) ⊜ first ⊖ second)
        BishopProperties.≃-refl
        (Alternating.magnitude dataSet zero)
        (Alternating.magnitude dataSet (suc zero)))

------------------------------------------------------------------------
-- Concrete Taylor brackets for represented sine and cosine.
------------------------------------------------------------------------

record LowOrderTaylorBrackets
    (dataSet : Elementary.BishopElementaryPowerSeriesData)
    (value : BishopReal.ℝ) : Set₁ where
  field
    sineLower :
      BishopReal._≤_
        (BishopReal._-_
          (Recurrence.sineMagnitudeTerm value zero)
          (Recurrence.sineMagnitudeTerm value (suc zero)))
        (Elementary.bishopSin dataSet value)

    sineUpper :
      BishopReal._≤_
        (Elementary.bishopSin dataSet value)
        (Recurrence.sineMagnitudeTerm value zero)

    cosineLower :
      BishopReal._≤_
        (BishopReal._-_
          (Recurrence.cosineMagnitudeTerm value zero)
          (Recurrence.cosineMagnitudeTerm value (suc zero)))
        (Elementary.bishopCos dataSet value)

    cosineUpper :
      BishopReal._≤_
        (Elementary.bishopCos dataSet value)
        (Recurrence.cosineMagnitudeTerm value zero)

open LowOrderTaylorBrackets public

lowOrderTaylorBrackets :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  LowOrderTaylorBrackets dataSet value
lowOrderTaylorBrackets {dataSet} {value} inputs =
  let
    concrete = Concrete.concreteSineCosineInterlacing inputs
    sineData = Concrete.sineAlternatingSeriesData inputs
    cosineData = Concrete.cosineAlternatingSeriesData inputs
    sineInterlacing = Interlacing.sineInterlacing concrete
    cosineInterlacing = Interlacing.cosineInterlacing concrete
  in
  record
    { sineLower =
        BishopProperties.≤-respˡ-≃
          (BishopProperties.≃-symm
            (lowerOneEquivalentFirstMinusSecondMagnitude sineData))
          (Interlacing.lowerPartialBelowRepresentedLimit
            sineInterlacing (suc zero))
    ; sineUpper =
        BishopProperties.≤-respʳ-≃
          (upperZeroEquivalentFirstMagnitude sineData)
          (Interlacing.representedLimitBelowUpperPartial
            sineInterlacing zero)
    ; cosineLower =
        BishopProperties.≤-respˡ-≃
          (BishopProperties.≃-symm
            (lowerOneEquivalentFirstMinusSecondMagnitude cosineData))
          (Interlacing.lowerPartialBelowRepresentedLimit
            cosineInterlacing (suc zero))
    ; cosineUpper =
        BishopProperties.≤-respʳ-≃
          (upperZeroEquivalentFirstMagnitude cosineData)
          (Interlacing.representedLimitBelowUpperPartial
            cosineInterlacing zero)
    }

------------------------------------------------------------------------
-- Signed first-omitted remainder control at the two useful truncations.
------------------------------------------------------------------------

sineFirstOmittedTail :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  FirstOmitted.SetoidSignedFirstOmittedTail
    FirstOmitted.bishopSetoidOrderedDifferenceKernel
sineFirstOmittedTail inputs =
  FirstOmitted.bishopAlternatingBracketsGiveFirstOmittedTail
    (Interlacing.sineInterlacing
      (Concrete.concreteSineCosineInterlacing inputs))

cosineFirstOmittedTail :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  FirstOmitted.SetoidSignedFirstOmittedTail
    FirstOmitted.bishopSetoidOrderedDifferenceKernel
cosineFirstOmittedTail inputs =
  FirstOmitted.bishopAlternatingBracketsGiveFirstOmittedTail
    (Interlacing.cosineInterlacing
      (Concrete.concreteSineCosineInterlacing inputs))

p33BishopLowOrderTaylorBracketLevel : ProofLevel
p33BishopLowOrderTaylorBracketLevel = machineChecked

p33BishopSignedFirstOmittedTailLevel : ProofLevel
p33BishopSignedFirstOmittedTailLevel = machineChecked
