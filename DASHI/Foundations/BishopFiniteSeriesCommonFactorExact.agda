module DASHI.Foundations.BishopFiniteSeriesCommonFactorExact where

------------------------------------------------------------------------
-- COMMON FACTOR FOR NATIVE FINITE SERIES SUMS
--
-- Pull a fixed right multiplier through the stdlib Fin-sum / Bishop SeriesOf
-- bridge once and for all:
--
--   sum_{j<n} (a_j * x)  ~=  (sum_{j<n} a_j) * x.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Unnormalised using (0ℚᵘ)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Foundations.BishopFinSumSeriesBridgeExact as FinSum
open import DASHI.Physics.YangMills.CompactLieProofLevel

finSumCommonFactor :
  (terms : Nat → BishopReal.ℝ) →
  (factor : BishopReal.ℝ) →
  ∀ count →
  BishopReal._≃_
    (FinSum.finSum
      (λ index → BishopReal._*_ (terms index) factor)
      count)
    (BishopReal._*_
      (FinSum.finSum terms count)
      factor)
finSumCommonFactor terms factor zero =
  let open BishopP.ℝ-Solver
  in solve 1
    (λ f → Κ 0ℚᵘ ⊜ Κ 0ℚᵘ ⊗ f)
    BishopP.≃-refl factor
finSumCommonFactor terms factor (suc count) =
  BishopP.≃-trans
    (FinSum.finSumSuccessor
      (λ index → BishopReal._*_ (terms index) factor)
      count)
    (BishopP.≃-trans
      (BishopP.+-congˡ
        (BishopReal._*_ (terms count) factor)
        (finSumCommonFactor terms factor count))
      (BishopP.≃-trans
        distributed
        (BishopP.*-congʳ
          (BishopP.≃-symm
            (FinSum.finSumSuccessor terms count)))))
  where
  distributed :
    BishopReal._≃_
      (BishopReal._+_
        (BishopReal._*_
          (FinSum.finSum terms count)
          factor)
        (BishopReal._*_ (terms count) factor))
      (BishopReal._*_
        (BishopReal._+_
          (FinSum.finSum terms count)
          (terms count))
        factor)
  distributed =
    let open BishopP.ℝ-Solver
    in solve 3
      (λ old term f →
        (old ⊗ f) ⊕ (term ⊗ f)
        ⊜ (old ⊕ term) ⊗ f)
      BishopP.≃-refl
      (FinSum.finSum terms count)
      (terms count)
      factor

seriesOfCommonFactor :
  (terms : Nat → BishopReal.ℝ) →
  (factor : BishopReal.ℝ) →
  ∀ count →
  BishopReal._≃_
    (FinSum.finSum
      (λ index → BishopReal._*_ (terms index) factor)
      count)
    (BishopReal._*_
      (BishopSequence.SeriesOf terms count)
      factor)
seriesOfCommonFactor terms factor count =
  BishopP.≃-trans
    (finSumCommonFactor terms factor count)
    (BishopP.*-congʳ
      (FinSum.finSumIsSeriesOf terms count))

bishopFiniteSeriesCommonFactorLevel : ProofLevel
bishopFiniteSeriesCommonFactorLevel = machineChecked
