module DASHI.Foundations.BishopFinSumSeriesBridgeExact where

------------------------------------------------------------------------
-- STDLIB Fin-SUM <-> NATIVE BISHOP SeriesOf
--
-- The stdlib binomial theorem is phrased using finite vectors indexed by Fin n,
-- while the pinned Bishop analysis library phrases series partial sums as
-- `SeriesOf`.  This module proves the finite bridge once and for all.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (Fin; toℕ)

import Algebra.Properties.Semiring.Sum as SemiringSum
import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

open import DASHI.Physics.YangMills.CompactLieProofLevel

module BishopSum = SemiringSum BishopP.+-*-semiring

finSum : (Nat → BishopReal.ℝ) → Nat → BishopReal.ℝ
finSum terms count =
  BishopSum.sum (λ index → terms (toℕ index))

finSumIsSeriesOf :
  (terms : Nat → BishopReal.ℝ) →
  ∀ count →
  BishopReal._≃_
    (finSum terms count)
    (BishopSequence.SeriesOf terms count)
finSumIsSeriesOf terms zero = BishopP.≃-refl
finSumIsSeriesOf terms (suc count) =
  BishopP.+-cong
    BishopP.≃-refl
    (finSumIsSeriesOf (λ n → terms (suc n)) count)

bishopFinSumSeriesBridgeLevel : ProofLevel
bishopFinSumSeriesBridgeLevel = machineChecked
