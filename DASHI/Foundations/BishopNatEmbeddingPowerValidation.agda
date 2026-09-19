module DASHI.Foundations.BishopNatEmbeddingPowerValidation where

open import Agda.Builtin.Nat using (Nat; suc; _*_)

import Real as BishopReal
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NatReal
import DASHI.Mathematics.NumberTheory.FiniteDivisorPowerSumExact as Divisor
import DASHI.Foundations.BishopNatEmbeddingPowerExact as P

natPowerEmbeddingRegression :
  ∀ base exponent →
  BishopReal._≃_
    (NatReal.natReal (Divisor.powNat base exponent))
    (BishopReal.pow (NatReal.natReal base) exponent)
natPowerEmbeddingRegression = P.natRealPowNat

natPowerTimesBaseEmbeddingRegression :
  ∀ base exponent →
  BishopReal._≃_
    (NatReal.natReal (Divisor.powNat base exponent * base))
    (BishopReal.pow (NatReal.natReal base) (suc exponent))
natPowerTimesBaseEmbeddingRegression =
  P.natRealPowNatTimesBase
