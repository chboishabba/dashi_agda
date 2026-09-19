module DASHI.Analysis.BishopPolynomialSuccessorFactorLimitValidation where

open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Analysis.BishopPolynomialSuccessorFactorLimitExact as P

fixedPowerLimitRegression :
  ∀ {sequence : Nat → BishopReal.ℝ} {limit : BishopReal.ℝ} →
  BishopSequence._ConvergesTo_ sequence limit →
  ∀ degree →
  BishopSequence._ConvergesTo_
    (λ index → BishopReal.pow (sequence index) degree)
    (BishopReal.pow limit degree)
fixedPowerLimitRegression = P.fixedPowerPreservesConvergence

successorFactorRegression :
  ∀ (ratio : BishopReal.ℝ) degree →
  BishopSequence._ConvergesTo_
    (P.polynomialSuccessorFactor ratio degree)
    ratio
successorFactorRegression = P.polynomialSuccessorFactorConverges

eventualUpperRegression :
  ∀ {ratio upper : BishopReal.ℝ} degree →
  BishopReal._<_ ratio upper →
  P.EventuallyBelow
    (P.polynomialSuccessorFactor ratio degree)
    upper
eventualUpperRegression = P.polynomialSuccessorFactorEventuallyBelow
