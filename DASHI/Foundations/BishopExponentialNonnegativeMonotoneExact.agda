module DASHI.Foundations.BishopExponentialNonnegativeMonotoneExact where

------------------------------------------------------------------------
-- MONOTONICITY OF THE CONCRETE EXPONENTIAL ON NONNEGATIVE INPUTS
--
-- For 0<=x<=y, Bishop's existing power monotonicity gives x^n<=y^n.
-- Multiplication by the nonnegative reciprocal-factorial coefficient preserves
-- order termwise; finite sums and then limits preserve the inequality.
--
-- No exp-additivity is used.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
open import DASHI.Physics.YangMills.CompactLieProofLevel

expTermMonotoneNonnegative :
  ∀ {left right : BishopReal.ℝ} →
  BishopReal.NonNegative left →
  BishopReal._≤_ left right →
  ∀ n →
  BishopReal._≤_
    (Exp.expTerm left n)
    (Exp.expTerm right n)
expTermMonotoneNonnegative leftNN left≤right n =
  BishopP.*-monoˡ-≤-nonNeg
    (BishopSequence.x≤y∧nonNegx⇒xⁿ≤yⁿ n left≤right leftNN)
    (Exp.embeddedInverseFactorialNonnegative n)

expPartialSumMonotoneNonnegative :
  ∀ {left right : BishopReal.ℝ} →
  BishopReal.NonNegative left →
  BishopReal._≤_ left right →
  ∀ count →
  BishopReal._≤_
    (BishopSequence.SeriesOf (Exp.expTerm left) count)
    (BishopSequence.SeriesOf (Exp.expTerm right) count)
expPartialSumMonotoneNonnegative leftNN left≤right =
  BishopSequence.∑₀-mono-≤
    (expTermMonotoneNonnegative leftNN left≤right)

bishopExpMonotoneNonnegative :
  ∀ {left right : BishopReal.ℝ} →
  BishopReal.NonNegative left →
  BishopReal._≤_ left right →
  BishopReal._≤_
    (Exp.bishopExp left)
    (Exp.bishopExp right)
bishopExpMonotoneNonnegative {left} {right} leftNN left≤right =
  BishopSequence.xₙ≤yₙ⇒limxₙ≤limyₙ
    (expPartialSumMonotoneNonnegative leftNN left≤right)
    (Exp.bishopExp left , Exp.bishopExpConverges left)
    (Exp.bishopExp right , Exp.bishopExpConverges right)

bishopExponentialNonnegativeMonotoneLevel : ProofLevel
bishopExponentialNonnegativeMonotoneLevel = machineChecked
