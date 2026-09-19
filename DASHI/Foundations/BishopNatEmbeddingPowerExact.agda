module DASHI.Foundations.BishopNatEmbeddingPowerExact where

------------------------------------------------------------------------
-- NATURAL POWERS COMMUTE WITH THE CANONICAL NAT -> BISHOP EMBEDDING
--
-- DASHI CONTRIBUTION
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopCubicTranslationIteratedExact as NatReal
import DASHI.Mathematics.NumberTheory.FiniteDivisorPowerSumExact as Divisor

natRealPowNat :
  ∀ base exponent →
  BishopReal._≃_
    (NatReal.natReal (Divisor.powNat base exponent))
    (BishopReal.pow (NatReal.natReal base) exponent)
natRealPowNat base zero =
  BishopP.≃-refl
natRealPowNat base (suc exponent) =
  BishopP.≃-trans
    (NatReal.natRealMul
      base
      (Divisor.powNat base exponent))
    (BishopP.≃-trans
      (BishopP.*-cong
        BishopP.≃-refl
        (natRealPowNat base exponent))
      (BishopP.*-comm
        (NatReal.natReal base)
        (BishopReal.pow (NatReal.natReal base) exponent)))
