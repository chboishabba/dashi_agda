module DASHI.Analysis.BishopNaturalScaleEmbeddingBridgeExact where

open import Agda.Builtin.Nat using (Nat; zero; suc)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Analysis.BishopSetoidPowerDerivativeNormalisationExact as Power
import DASHI.Foundations.BishopExponentialBinomialCoefficientExact as Binomial
import DASHI.Foundations.BishopFiniteDegreeOneGeometricIdentityExact as NatReal

------------------------------------------------------------------------
-- RECURSIVE NATURAL SCALING = BISHOP SEMIRING NATURAL SCALING
------------------------------------------------------------------------

recursiveScaleIsSemiringScale :
  ∀ n value →
  Bishop._≃_
    (Power.natScale n value)
    (Binomial.BishopSemiringMult._×_ n value)
recursiveScaleIsSemiringScale zero value = BishopP.≃-refl
recursiveScaleIsSemiringScale (suc n) value =
  BishopP.≃-trans
    (BishopP.+-cong
      (recursiveScaleIsSemiringScale n value)
      BishopP.≃-refl)
    (BishopP.+-comm
      (Binomial.BishopSemiringMult._×_ n value)
      value)

recursiveScaleIsEmbeddedNaturalMultiply :
  ∀ n value →
  Bishop._≃_
    (Power.natScale n value)
    (Bishop._*_
      (NatReal.natReal n)
      value)
recursiveScaleIsEmbeddedNaturalMultiply n value =
  BishopP.≃-trans
    (recursiveScaleIsSemiringScale n value)
    (Binomial.naturalScaleAsEmbeddedMultiply n value)
