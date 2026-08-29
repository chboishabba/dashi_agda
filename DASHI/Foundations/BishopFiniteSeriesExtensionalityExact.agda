module DASHI.Foundations.BishopFiniteSeriesExtensionalityExact where

------------------------------------------------------------------------
-- NATIVE BISHOP SERIES EXTENSIONALITY
--
-- The legacy ConstructiveSeries layer had an abstract series-extensionality
-- authority.  On the pinned Bishop backend it follows directly from finite-sum
-- congruence, convergence transport, and uniqueness of limits.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

open import DASHI.Physics.YangMills.CompactLieProofLevel

finiteSumCongruent :
  ∀ {left right : Nat → BishopReal.ℝ} →
  (∀ n → BishopReal._≃_ (left n) (right n)) →
  ∀ count →
  BishopReal._≃_
    (BishopSequence.∑₀ left count)
    (BishopSequence.∑₀ right count)
finiteSumCongruent termCongruence zero = BishopP.≃-refl
finiteSumCongruent termCongruence (suc count) =
  BishopP.+-cong
    (finiteSumCongruent termCongruence count)
    (termCongruence count)

seriesPartialSumsCongruent :
  ∀ {left right : Nat → BishopReal.ℝ} →
  (∀ n → BishopReal._≃_ (left n) (right n)) →
  ∀ count →
  BishopReal._≃_
    (BishopSequence.SeriesOf left count)
    (BishopSequence.SeriesOf right count)
seriesPartialSumsCongruent termCongruence =
  finiteSumCongruent termCongruence

termwiseEquivalentSeriesHaveEquivalentLimits :
  ∀ {left right : Nat → BishopReal.ℝ}
    {leftLimit rightLimit : BishopReal.ℝ} →
  (∀ n → BishopReal._≃_ (left n) (right n)) →
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf left) leftLimit →
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf right) rightLimit →
  BishopReal._≃_ leftLimit rightLimit
termwiseEquivalentSeriesHaveEquivalentLimits
  {leftLimit = leftLimit}
  termCongruence leftConverges rightConverges =
  BishopSequence.uniqueness-of-limits
    (BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
      (seriesPartialSumsCongruent termCongruence)
      (leftLimit , leftConverges))
    rightConverges

bishopFiniteSeriesExtensionalityLevel : ProofLevel
bishopFiniteSeriesExtensionalityLevel = machineChecked
