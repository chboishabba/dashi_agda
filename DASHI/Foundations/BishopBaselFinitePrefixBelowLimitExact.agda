module DASHI.Foundations.BishopBaselFinitePrefixBelowLimitExact where

------------------------------------------------------------------------
-- FINITE BASEL PREFIX <= CONSTRUCTED BASEL LIMIT
--
-- The Basel terms are nonnegative, so their partial sums are increasing.  For
-- any fixed prefix N, compare the constant sequence S_N with the shifted
-- partial-sum subsequence S_(m+N).  The latter converges to the same Basel limit;
-- order of limits then yields
--
--   S_N <= baselLimit.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc; _+_)
import Data.Nat.Properties as NatP

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Foundations.BishopBaselReciprocalSquareConvergenceExact as Basel
import DASHI.Foundations.BishopFiniteRectangleInsideCauchyTriangleExact as FiniteOrder
open import DASHI.Physics.YangMills.CompactLieProofLevel

baselPartials : Nat → BishopReal.ℝ
baselPartials = BishopSequence.SeriesOf Basel.baselTerm

baselPartialsIncreasing : BishopSequence._isIncreasing baselPartials
baselPartialsIncreasing =
  FiniteOrder.partialSumsIncreasing Basel.baselTermNonnegative

shiftedBaselPartials : Nat → Nat → BishopReal.ℝ
shiftedBaselPartials count index = baselPartials (index + count)

shiftedBaselPartialsSubsequence :
  ∀ count →
  BishopSequence._SubsequenceOf_
    (shiftedBaselPartials count)
    baselPartials
shiftedBaselPartialsSubsequence count =
  BishopSequence.subseq*
    ((λ index → index + count)
    , (λ index → BishopP.≃-refl)
    , (λ index → NatP.n<1+n (index + count)))

shiftedBaselPartialsConverges :
  ∀ count →
  BishopSequence._ConvergesTo_
    (shiftedBaselPartials count)
    Basel.baselLimit
shiftedBaselPartialsConverges count =
  BishopSequence.xₙ⊆yₙ∧yₙ→y⇒xₙ→y
    (shiftedBaselPartialsSubsequence count)
    Basel.baselSeriesConvergent

constantPrefix : Nat → Nat → BishopReal.ℝ
constantPrefix count index = baselPartials count

constantPrefixConvergent :
  ∀ count →
  BishopSequence._isConvergent (constantPrefix count)
constantPrefixConvergent count =
  baselPartials count
  , BishopSequence.xₙ≃c⇒xₙ→c
      (λ {(suc index) → BishopP.≃-refl})

shiftedPrefixConvergent :
  ∀ count →
  BishopSequence._isConvergent (shiftedBaselPartials count)
shiftedPrefixConvergent count =
  Basel.baselLimit , shiftedBaselPartialsConverges count

constantPrefixBelowShifted :
  ∀ count index →
  BishopReal._≤_
    (constantPrefix count index)
    (shiftedBaselPartials count index)
constantPrefixBelowShifted count index =
  BishopSequence.isIncreasing⇒isIncreasing₂
    baselPartialsIncreasing
    (index + count)
    count
    (NatP.m≤n+m count index)

baselFinitePrefixBelowLimit :
  ∀ count →
  BishopReal._≤_
    (BishopSequence.SeriesOf Basel.baselTerm count)
    Basel.baselLimit
baselFinitePrefixBelowLimit count =
  BishopSequence.xₙ≤yₙ⇒limxₙ≤limyₙ
    (constantPrefixBelowShifted count)
    (constantPrefixConvergent count)
    (shiftedPrefixConvergent count)

bishopBaselFinitePrefixBelowLimitLevel : ProofLevel
bishopBaselFinitePrefixBelowLimitLevel = machineChecked
