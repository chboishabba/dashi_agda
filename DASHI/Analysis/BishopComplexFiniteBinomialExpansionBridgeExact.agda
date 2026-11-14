module DASHI.Analysis.BishopComplexFiniteBinomialExpansionBridgeExact where

------------------------------------------------------------------------
-- NATIVE COMPLEX STDLIB FIN SUM -> TWO ORIGINAL BISHOP REAL FIN SUMS.
--
-- This is a generic proof that the stdlib semiring finite sum of
-- original BishopComplex values is componentwise the original Bishop
-- REAL semiring Fin sum. In particular the stdlib complex binomial
-- expansion matches an explicit, actual pair of Bishop Fin sums.
--
-- No equality by fiat between different finite-sum presentations.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base as Fin using (Fin; inject₁; fromℕ; toℕ)
open import Data.Product.Base using (_,_; proj₁; proj₂)

import Algebra.Properties.Semiring.Sum as SemiringSum
import RealProperties as BishopP
import Data.Nat.Base as Nat
import Data.Nat.Combinatorics as Comb
import DASHI.Foundations.BishopFiniteDegreeOneGeometricIdentityExact as NatReal
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexCommutativeSemiringExact as Semiring
import DASHI.Analysis.BishopComplexFiniteBinomialTheoremExact as Binomial
import DASHI.Analysis.BishopComplexFiniteBinomialScaleExact as Scale

module OriginalComplexSum =
  SemiringSum Semiring.originalBishopComplexSemiring

module OriginalRealSum =
  SemiringSum BishopP.+-*-semiring

originalBishopComplexFinSumCoordinates :
  ∀ {n} (terms : Fin n → Complex.BishopComplex) →
  Complex._≈C_
    (OriginalComplexSum.sum terms)
    (Complex.complex
      (OriginalRealSum.sum (λ index → Complex.re (terms index)))
      (OriginalRealSum.sum (λ index → Complex.im (terms index))))
originalBishopComplexFinSumCoordinates {zero} terms =
  Complex.≈C-refl Algebra.zeroC
originalBishopComplexFinSumCoordinates {suc n} terms =
  let
    prefix : Fin n → Complex.BishopComplex
    prefix index = terms (inject₁ index)
    last = terms (fromℕ n)
    before =
      OriginalComplexSum.sum-init-last terms
    recurse =
      Algebra.addCCongruent
        (originalBishopComplexFinSumCoordinates prefix)
        (Complex.≈C-refl last)
    finish =
      (BishopP.≃-symm
        (OriginalRealSum.sum-init-last
          (λ index → Complex.re (terms index))))
      ,
      (BishopP.≃-symm
        (OriginalRealSum.sum-init-last
          (λ index → Complex.im (terms index))))
  in
  Binomial.complexTrans before
    (Binomial.complexTrans recurse finish)

originalBishopStdlibComplexBinomialExpansionCoordinates :
  ∀ z w n →
  Complex._≈C_
    (Binomial.OriginalComplexBinomial.binomialExpansion z w n)
    (Complex.complex
      (OriginalRealSum.sum
        (λ index →
          Complex.re
            (Binomial.OriginalComplexBinomial.binomialTerm
              z w n index)))
      (OriginalRealSum.sum
        (λ index →
          Complex.im
            (Binomial.OriginalComplexBinomial.binomialTerm
              z w n index))))
originalBishopStdlibComplexBinomialExpansionCoordinates z w n =
  originalBishopComplexFinSumCoordinates
    (Binomial.OriginalComplexBinomial.binomialTerm z w n)

originalBishopBinomialExpansionUsesOriginalPowers :
  ∀ z w n →
  Complex._≈C_
    (Binomial.OriginalComplexBinomial.binomialExpansion z w n)
    (Complex.complex
      (OriginalRealSum.sum
        (λ index →
          Complex.re
            (Algebra.scaleC
              (NatReal.natReal
                (n Comb.C toℕ index))
              (Algebra._*C_
                (Algebra.powC z (toℕ index))
                (Algebra.powC w (n Nat.∸ toℕ index))))))
      (OriginalRealSum.sum
        (λ index →
          Complex.im
            (Algebra.scaleC
              (NatReal.natReal
                (n Comb.C toℕ index))
              (Algebra._*C_
                (Algebra.powC z (toℕ index))
                (Algebra.powC w (n Nat.∸ toℕ index)))))))
originalBishopBinomialExpansionUsesOriginalPowers z w n =
  Binomial.complexTrans
    (originalBishopStdlibComplexBinomialExpansionCoordinates z w n)
    (OriginalRealSum.sum-cong-≋
      (λ index →
        proj₁ (Scale.originalBishopComplexBinomialTermIsNative z w n index))
    ,
    OriginalRealSum.sum-cong-≋
      (λ index →
        proj₂ (Scale.originalBishopComplexBinomialTermIsNative z w n index)))
