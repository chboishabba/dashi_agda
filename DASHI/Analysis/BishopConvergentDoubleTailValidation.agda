module DASHI.Analysis.BishopConvergentDoubleTailValidation where

open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal
import Sequence as BishopSequence
import DASHI.Analysis.BishopConvergentDoubleTailExact as P

doubleTailRegression :
  ∀ {sequence : Nat → BishopReal.ℝ}
    {limit : BishopReal.ℝ} →
  BishopSequence._ConvergesTo_ sequence limit →
  BishopSequence._ConvergesTo_
    (λ index →
      BishopReal._-_
        (sequence (P.double index))
        (sequence index))
    BishopReal.0ℝ
doubleTailRegression = P.doubleTailConvergesZero
