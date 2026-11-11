module DASHI.Analysis.BishopComplexFactorialBinomialSummandExact where

------------------------------------------------------------------------
-- ORIGINAL BISHOP-COMPLEX FACTORIAL CONVOLUTION SUMMAND.
--
-- For k <= n, prove on the actual Bishop complex carrier:
--
--  (z^k/k!) *C (w^(n-k)/(n-k)!)
--   ~= scaleC (choose(n,k) * (1/n!)) (z^k *C w^(n-k)).
--
-- The reciprocal-factorial arithmetic is NOT re-proved: we reuse
-- BishopExponentialBinomialCoefficientExact.
--
-- This is a finite summand identity, not yet the entire complex
-- binomial theorem or any limit interchange.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as ℕ
import Data.Nat.Combinatorics as Comb
open import Data.Product.Base using (_,_; proj₁; proj₂)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Foundations.BishopExponentialBinomialCoefficientExact as Coeff
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopFiniteDegreeOneGeometricIdentityExact as NatReal
import DASHI.Moonshine.AbelBishopFactorialComplexRealAxisTermsExact as Factorial

complexTrans :
  ∀ {a b c : Complex.BishopComplex} →
  Complex._≈C_ a b → Complex._≈C_ b c → Complex._≈C_ a c
complexTrans first second =
  BishopP.≃-trans (proj₁ first) (proj₁ second)
  ,
  BishopP.≃-trans (proj₂ first) (proj₂ second)

-- Exact Cartesian multiplication compatibility with two original
-- Bishop real scalars, on arbitrary complex values.
originalBishopComplexTwoScalesMultiply :
  ∀ c d z w →
  Complex._≈C_
    (Algebra._*C_
      (Algebra.scaleC c z)
      (Algebra.scaleC d w))
    (Algebra.scaleC
      (BishopReal._*_ c d)
      (Algebra._*C_ z w))
originalBishopComplexTwoScalesMultiply
  c d (Complex.complex a b) (Complex.complex e f) =
  (let open BishopP.ℝ-Solver in
   solve 6
     (λ c′ d′ a′ b′ e′ f′ →
       ((c′ ⊗ a′) ⊗ (d′ ⊗ e′))
         ⊖ ((c′ ⊗ b′) ⊗ (d′ ⊗ f′))
       ⊜
       (c′ ⊗ d′) ⊗
         ((a′ ⊗ e′) ⊖ (b′ ⊗ f′)))
     BishopP.≃-refl c d a b e f)
  ,
  (let open BishopP.ℝ-Solver in
   solve 6
     (λ c′ d′ a′ b′ e′ f′ →
       ((c′ ⊗ a′) ⊗ (d′ ⊗ f′))
         ⊕ ((c′ ⊗ b′) ⊗ (d′ ⊗ e′))
       ⊜
       (c′ ⊗ d′) ⊗
         ((a′ ⊗ f′) ⊕ (b′ ⊗ e′)))
     BishopP.≃-refl c d a b e f)

originalBishopComplexScaleCongruent :
  ∀ {c d} →
  BishopReal._≃_ c d →
  ∀ z →
  Complex._≈C_
    (Algebra.scaleC c z)
    (Algebra.scaleC d z)
originalBishopComplexScaleCongruent c≃d
  (Complex.complex a b) =
  (BishopP.*-congʳ c≃d)
  ,
  (BishopP.*-congʳ c≃d)

originalBishopComplexFactorialConvolutionSummand :
  (z w : Complex.BishopComplex) →
  ∀ n k →
  k ℕ.≤ n →
  Complex._≈C_
    (Algebra._*C_
      (Factorial.originalBishopFactorialComplexTerm z k)
      (Factorial.originalBishopFactorialComplexTerm w (n ℕ.∸ k)))
    (Algebra.scaleC
      (BishopReal._*_
        (NatReal.natReal (n Comb.C k))
        (Exp.embed (Exp.inverseFactorial n)))
      (Algebra._*C_
        (Algebra.powC z k)
        (Algebra.powC w (n ℕ.∸ k))))
originalBishopComplexFactorialConvolutionSummand
  z w n k k≤n =
  complexTrans
    (originalBishopComplexTwoScalesMultiply
      (Exp.embed (Exp.inverseFactorial k))
      (Exp.embed (Exp.inverseFactorial (n ℕ.∸ k)))
      (Algebra.powC z k)
      (Algebra.powC w (n ℕ.∸ k)))
    (originalBishopComplexScaleCongruent
      (Coeff.embeddedInverseFactorialProductBinomial k≤n)
      (Algebra._*C_
        (Algebra.powC z k)
        (Algebra.powC w (n ℕ.∸ k))))
