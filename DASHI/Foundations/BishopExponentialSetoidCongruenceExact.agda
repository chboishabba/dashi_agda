module DASHI.Foundations.BishopExponentialSetoidCongruenceExact where

------------------------------------------------------------------------
-- SETOID CONGRUENCE OF THE CONCRETE EXPONENTIAL
--
-- The concrete exponential is defined as the Bishop limit of x^n/n!.  Since
-- power and finite sums respect Bishop equality, equivalent inputs have
-- termwise equivalent exponential series and hence equivalent limits.
--
-- No exp-additivity or monotonicity is assumed.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as SeriesExt
open import DASHI.Physics.YangMills.CompactLieProofLevel

powCongruent :
  ∀ {left right : BishopReal.ℝ} →
  BishopReal._≃_ left right →
  ∀ n →
  BishopReal._≃_
    (BishopReal.pow left n)
    (BishopReal.pow right n)
powCongruent equivalent zero = BishopP.≃-refl
powCongruent equivalent (suc n) =
  BishopP.*-cong (powCongruent equivalent n) equivalent

expTermCongruent :
  ∀ {left right : BishopReal.ℝ} →
  BishopReal._≃_ left right →
  ∀ n →
  BishopReal._≃_
    (Exp.expTerm left n)
    (Exp.expTerm right n)
expTermCongruent equivalent n =
  BishopP.*-congʳ (powCongruent equivalent n)

bishopExpCongruent :
  ∀ {left right : BishopReal.ℝ} →
  BishopReal._≃_ left right →
  BishopReal._≃_
    (Exp.bishopExp left)
    (Exp.bishopExp right)
bishopExpCongruent equivalent =
  SeriesExt.termwiseEquivalentSeriesHaveEquivalentLimits
    (expTermCongruent equivalent)
    (Exp.bishopExpConverges _)
    (Exp.bishopExpConverges _)

bishopExponentialSetoidCongruenceLevel : ProofLevel
bishopExponentialSetoidCongruenceLevel = machineChecked
