module DASHI.Foundations.BishopBaselFiniteCommonFactorExact where

------------------------------------------------------------------------
-- BASEL FINITE PREFIX WITH A COMMON FACTOR
--
-- Specialize the generic finite-series common-factor theorem to the exact
-- Basel sequence used by the convergence owner.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Foundations.BishopBaselReciprocalSquareConvergenceExact as Basel
import DASHI.Foundations.BishopFiniteSeriesCommonFactorExact as Common
import DASHI.Foundations.BishopFinSumSeriesBridgeExact as FinSum
open import DASHI.Physics.YangMills.CompactLieProofLevel

scaledBaselFinitePrefix : BishopReal.ℝ → Nat → BishopReal.ℝ
scaledBaselFinitePrefix factor count =
  FinSum.finSum
    (λ index → BishopReal._*_ (Basel.baselTerm index) factor)
    count

scaledBaselFinitePrefixCommonFactor :
  (factor : BishopReal.ℝ) →
  ∀ count →
  BishopReal._≃_
    (scaledBaselFinitePrefix factor count)
    (BishopReal._*_
      (BishopSequence.SeriesOf Basel.baselTerm count)
      factor)
scaledBaselFinitePrefixCommonFactor factor count =
  Common.seriesOfCommonFactor Basel.baselTerm factor count

bishopBaselFiniteCommonFactorLevel : ProofLevel
bishopBaselFiniteCommonFactorLevel = machineChecked
