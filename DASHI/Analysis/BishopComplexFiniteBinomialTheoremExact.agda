module DASHI.Analysis.BishopComplexFiniteBinomialTheoremExact where

------------------------------------------------------------------------
-- ACTUAL BISHOP COMPLEX POWER BINOMIAL THEOREM.
--
-- Instantiate the SAME stdlib Algebra.Properties.CommutativeSemiring.Binomial
-- theorem already used for the original real exponential Cauchy
-- coefficient, but now on the source Cartesian Bishop complex semiring.
--
-- The finite source powC z n multiplies its recurrence on the left,
-- as does the stdlib semiring exponent. Their exact setoid equality
-- is proved by induction on n.
--
-- This establishes the actual finite complex binomial *power*
-- identity, not yet the natural scale / factorial coefficient weld.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product.Base using (_,_; proj₁; proj₂)

import Algebra.Properties.CommutativeSemiring.Binomial as Binomial
import Algebra.Properties.Semiring.Exp as SemiringExp

import RealProperties as BishopP
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexCommutativeSemiringExact as Semiring

module OriginalComplexBinomial =
  Binomial Semiring.originalBishopComplexCommutativeSemiring

module OriginalComplexExp =
  SemiringExp Semiring.originalBishopComplexSemiring

complexTrans :
  ∀ {a b c : Complex.BishopComplex} →
  Complex._≈C_ a b →
  Complex._≈C_ b c →
  Complex._≈C_ a c
complexTrans first second =
  BishopP.≃-trans (proj₁ first) (proj₁ second)
  ,
  BishopP.≃-trans (proj₂ first) (proj₂ second)

complexSym :
  ∀ {a b : Complex.BishopComplex} →
  Complex._≈C_ a b →
  Complex._≈C_ b a
complexSym equivalence =
  BishopP.≃-symm (proj₁ equivalence)
  ,
  BishopP.≃-symm (proj₂ equivalence)

originalBishopStdlibPowerIsNative :
  ∀ z n →
  Complex._≈C_
    (OriginalComplexExp._^_ z n)
    (Algebra.powC z n)
originalBishopStdlibPowerIsNative z zero =
  Complex.≈C-refl Algebra.oneC
originalBishopStdlibPowerIsNative z (suc n) =
  Algebra.mulCCongruent
    (Complex.≈C-refl z)
    (originalBishopStdlibPowerIsNative z n)

originalBishopComplexFiniteBinomialPower :
  ∀ z w n →
  Complex._≈C_
    (Algebra.powC (Algebra._+C_ z w) n)
    (OriginalComplexBinomial.binomialExpansion z w n)
originalBishopComplexFiniteBinomialPower z w n =
  complexTrans
    (complexSym
      (originalBishopStdlibPowerIsNative
        (Algebra._+C_ z w) n))
    (OriginalComplexBinomial.theorem n z w)
