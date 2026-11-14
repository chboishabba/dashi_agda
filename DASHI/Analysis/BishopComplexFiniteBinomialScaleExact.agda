module DASHI.Analysis.BishopComplexFiniteBinomialScaleExact where

------------------------------------------------------------------------
-- ACTUAL COMPLEX NATURAL SCALING / FACTORIAL BINOMIAL BRIDGE.
--
-- Reuse original real natReal n ↔ stdlib n × x theorem componentwise.
-- No rational division, new nat embedding, or parallel complex ring.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (Fin; toℕ)
import Data.Nat.Base as ℕ
import Data.Nat.Combinatorics as Comb
open import Data.Product.Base using (_,_)

import Algebra.Properties.Semiring.Mult as SemiringMult
import Real as BishopReal
import RealProperties as BishopP

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexCommutativeSemiringExact as Semiring
import DASHI.Analysis.BishopComplexFiniteBinomialTheoremExact as Binomial
import DASHI.Foundations.BishopExponentialBinomialCoefficientExact as RealBinomial
import DASHI.Foundations.BishopFiniteDegreeOneGeometricIdentityExact as NatReal

module OriginalComplexMult =
  SemiringMult Semiring.originalBishopComplexSemiring

complexNatMultCoordinates :
  ∀ n (z : Complex.BishopComplex) →
  Complex._≈C_
    (OriginalComplexMult._×_ n z)
    (Complex.complex
      (RealBinomial.BishopSemiringMult._×_ n (Complex.re z))
      (RealBinomial.BishopSemiringMult._×_ n (Complex.im z)))
complexNatMultCoordinates zero (Complex.complex a b) =
  Complex.≈C-refl Algebra.zeroC
complexNatMultCoordinates (suc n) (Complex.complex a b) =
  Algebra.addCCongruent
    (Complex.≈C-refl (Complex.complex a b))
    (complexNatMultCoordinates n (Complex.complex a b))

originalBishopComplexNatScaleAsBishopReal :
  ∀ n (z : Complex.BishopComplex) →
  Complex._≈C_
    (OriginalComplexMult._×_ n z)
    (Algebra.scaleC (NatReal.natReal n) z)
originalBishopComplexNatScaleAsBishopReal n
  (Complex.complex a b) =
  Binomial.complexTrans
    (complexNatMultCoordinates n (Complex.complex a b))
    (RealBinomial.naturalScaleAsEmbeddedMultiply n a
     ,
     RealBinomial.naturalScaleAsEmbeddedMultiply n b)

originalBishopComplexNestedScale :
  ∀ c d (z : Complex.BishopComplex) →
  Complex._≈C_
    (Algebra.scaleC c (Algebra.scaleC d z))
    (Algebra.scaleC (BishopReal._*_ c d) z)
originalBishopComplexNestedScale c d (Complex.complex a b) =
  (let open BishopP.ℝ-Solver in
   solve 3
     (λ c′ d′ a′ → c′ ⊗ (d′ ⊗ a′) ⊜ (c′ ⊗ d′) ⊗ a′)
     BishopP.≃-refl c d a)
  ,
  (let open BishopP.ℝ-Solver in
   solve 3
     (λ c′ d′ b′ → c′ ⊗ (d′ ⊗ b′) ⊜ (c′ ⊗ d′) ⊗ b′)
     BishopP.≃-refl c d b)

-- The stdlib binomial summand is nCk × (stdlib z^k * stdlib w^(n-k)).
-- These source equalities identify every part with original powC,
-- original natural scale and original Bishop complex operations.
originalBishopComplexBinomialTermIsNative :
  ∀ z w n (index : Fin (suc n)) →
  Complex._≈C_
    (Binomial.OriginalComplexBinomial.binomialTerm z w n index)
    (Algebra.scaleC
      (NatReal.natReal (n Comb.C toℕ index))
      (Algebra._*C_
        (Algebra.powC z (toℕ index))
        (Algebra.powC w (n ℕ.∸ toℕ index))))
originalBishopComplexBinomialTermIsNative z w n index =
  let
    k = toℕ index
    m = n ℕ.∸ k
    choose = n Comb.C k
    powers =
      Algebra.mulCCongruent
        (Binomial.originalBishopStdlibPowerIsNative z k)
        (Binomial.originalBishopStdlibPowerIsNative w m)
  in
  Binomial.complexTrans
    (originalBishopComplexNatScaleAsBishopReal
      choose
      (Algebra._*C_
        (Binomial.OriginalComplexExp._^_ z k)
        (Binomial.OriginalComplexExp._^_ w m)))
    (Algebra.scaleCCongruent powers (NatReal.natReal choose))
