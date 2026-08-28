module DASHI.Foundations.BishopAbsoluteSeriesTailExact where

------------------------------------------------------------------------
-- QUANTITATIVE TAILS FROM THE PINNED BISHOP CAUCHY TEST
--
-- For an absolutely convergent Bishop series, the finite tail of absolute
-- values is eventually <= 1/k.  This is not a new convergence axiom: it is a
-- direct specialization of Sequence.cauchyConvergenceTest-if to |a_n|,
-- followed by x <= |x|.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (_,_; proj₁; proj₂)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

open import DASHI.Physics.YangMills.CompactLieProofLevel

absoluteTailCutoff :
  ∀ {terms : Nat → BishopReal.ℝ} →
  BishopSequence.SeriesOf_ConvergesAbsolutely terms →
  (k : Nat) → .{{_ : ℕ.NonZero k}} →
  Nat
absoluteTailCutoff {terms} absolute k =
  suc (proj₁
    (BishopSequence.cauchyConvergenceTest-if
      (λ n → BishopReal.∣ terms n ∣)
      absolute
      k))

absoluteFiniteTailSmall :
  ∀ {terms : Nat → BishopReal.ℝ} →
  (absolute : BishopSequence.SeriesOf_ConvergesAbsolutely terms) →
  (k : Nat) → .{{_ : ℕ.NonZero k}} →
  ∀ m n →
  m ℕ.≥ absoluteTailCutoff absolute k →
  n ℕ.≥ absoluteTailCutoff absolute k →
  BishopReal._≤_
    (BishopSequence.∑ (λ i → BishopReal.∣ terms i ∣) m n)
    (BishopReal._⋆ (+ 1 / k))
absoluteFiniteTailSmall {terms} absolute k m n mPast nPast =
  BishopP.≤-trans
    BishopP.x≤∣x∣
    (proj₂
      (BishopSequence.cauchyConvergenceTest-if
        (λ i → BishopReal.∣ terms i ∣)
        absolute
        k)
      m n mPast nPast)

absoluteSeriesTailLevel : ProofLevel
absoluteSeriesTailLevel = machineChecked
