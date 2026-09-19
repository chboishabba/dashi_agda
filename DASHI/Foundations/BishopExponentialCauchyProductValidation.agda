module DASHI.Foundations.BishopExponentialCauchyProductValidation where

import Real as BishopReal
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialCauchyProductExact as P

expAddRegression :
  ∀ left right →
  BishopReal._≃_
    (Exp.bishopExp (BishopReal._+_ left right))
    (BishopReal._*_ (Exp.bishopExp left) (Exp.bishopExp right))
expAddRegression = P.bishopExpAdd

reciprocalProductRegression :
  ∀ value →
  BishopReal._≃_
    (BishopReal._*_ (Exp.bishopExp value) (Exp.bishopExp (BishopReal.- value)))
    BishopReal.1ℝ
reciprocalProductRegression = P.bishopExpTimesNegativeIsOne
