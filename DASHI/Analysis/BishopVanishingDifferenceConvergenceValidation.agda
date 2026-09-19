module DASHI.Analysis.BishopVanishingDifferenceConvergenceValidation where

open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal
import Sequence as BishopSequence
import DASHI.Analysis.BishopVanishingDifferenceConvergenceExact as P

vanishingDifferenceRegression :
  ∀ {left right error : Nat → BishopReal.ℝ}
    {limit : BishopReal.ℝ} →
  BishopSequence._ConvergesTo_ right limit →
  BishopSequence._ConvergesTo_ error BishopReal.0ℝ →
  (∀ index →
    BishopReal._≤_
      (BishopReal.∣ BishopReal._-_ (left index) (right index) ∣)
      (BishopReal.∣ error index ∣)) →
  BishopSequence._ConvergesTo_ left limit
vanishingDifferenceRegression = P.vanishingDifferenceConvergence
