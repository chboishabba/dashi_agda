module DASHI.Foundations.BishopFinSumSeriesBridgeExact where

------------------------------------------------------------------------
-- STDLIB Fin-SUM <-> NATIVE BISHOP SeriesOf
--
-- The stdlib binomial theorem is phrased using finite vectors indexed by Fin n,
-- while the pinned Bishop analysis library phrases series partial sums as
-- `SeriesOf`.  This module proves the finite bridge once and for all.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (toℕ)

import Algebra.Properties.Semiring.Sum as SemiringSum
import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

open import DASHI.Physics.YangMills.CompactLieProofLevel

module BishopSum = SemiringSum BishopP.+-*-semiring

finSum : (Nat → BishopReal.ℝ) → Nat → BishopReal.ℝ
finSum terms count =
  BishopSum.sum (λ index → terms (toℕ index))

finSumSuccessor :
  (terms : Nat → BishopReal.ℝ) →
  ∀ count →
  BishopReal._≃_
    (finSum terms (suc count))
    (BishopReal._+_ (finSum terms count) (terms count))
finSumSuccessor terms count =
  BishopSum.sum-init-last (λ index → terms (toℕ index))

finSumIsSeriesOf :
  (terms : Nat → BishopReal.ℝ) →
  ∀ count →
  BishopReal._≃_
    (finSum terms count)
    (BishopSequence.SeriesOf terms count)
finSumIsSeriesOf terms zero = BishopP.≃-refl
finSumIsSeriesOf terms (suc count) =
  BishopP.≃-trans
    (finSumSuccessor terms count)
    (BishopP.+-congˡ
      (terms count)
      (finSumIsSeriesOf terms count))

bishopFinSumSeriesBridgeLevel : ProofLevel
bishopFinSumSeriesBridgeLevel = machineChecked
