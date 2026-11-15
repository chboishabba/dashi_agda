module DASHI.Moonshine.AbelBishopInverseKoenigsRemainderFactorExact where

------------------------------------------------------------------------
-- ORIGINAL BISHOP COMPLEX: INVERSE-ORBIT DIFFERENCE FACTORIZATION.
--
-- R_p(w) = (g(w) - p) - p^-1 * (w - p)
--
-- For any selected source p with genuine BishopComplexNonzero witness,
-- any selected endomap g, and every original orbit:
--
--  h_(n+1)(z) - h_n(z)  ≈C
--     p^n * (p * R_p(g^n(z))).
--
-- No claim that the selected R_p has a quadratic bound. This is
-- the exact finite algebraic interface to the source Taylor bound.
--
-- Reuse: original BishopComplexAlgebraExact; complex semiring laws;
-- BishopComplexReciprocalExact; existing inverse-Koenigs orbit.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym)
open import Data.Product.Base using (_,_; proj₁; proj₂)

import RealProperties as BishopP
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexReciprocalExact as Reciprocal
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as Laws
import DASHI.Moonshine.AbelBishopInverseKoenigsFiniteOrbitExact as Orbit
import DASHI.Moonshine.AbelBishopKoenigsFiniteTelescopingExact as Telescope

open Algebra using (_+C_; _-C_; _*C_; powC)

complexTrans :
  ∀ {a b c : Complex.BishopComplex} →
  Complex._≈C_ a b →
  Complex._≈C_ b c →
  Complex._≈C_ a c
complexTrans u v =
  BishopP.≃-trans (proj₁ u) (proj₁ v) ,
  BishopP.≃-trans (proj₂ u) (proj₂ v)

complexSym :
  ∀ {a b : Complex.BishopComplex} →
  Complex._≈C_ a b →
  Complex._≈C_ b a
complexSym u =
  BishopP.≃-symm (proj₁ u) ,
  BishopP.≃-symm (proj₂ u)

-- Direct Bishop real ring normalization, coordinate by coordinate:
-- z * (x - y) = z*x - z*y.
complexMultiplyDifference :
  ∀ p u v →
  Complex._≈C_
    (p *C (u -C v))
    ((p *C u) -C (p *C v))
complexMultiplyDifference
  (Complex.complex a b)
  (Complex.complex c d)
  (Complex.complex e f) =
  (let open BishopP.ℝ-Solver in
    solve 6
      (λ a′ b′ c′ d′ e′ f′ →
        (a′ ⊗ (c′ ⊖ e′)) ⊖ (b′ ⊗ (d′ ⊖ f′))
        ⊜
        ((a′ ⊗ c′) ⊖ (b′ ⊗ d′))
          ⊖ ((a′ ⊗ e′) ⊖ (b′ ⊗ f′)))
      BishopP.≃-refl a b c d e f)
  ,
  (let open BishopP.ℝ-Solver in
    solve 6
      (λ a′ b′ c′ d′ e′ f′ →
        (a′ ⊗ (d′ ⊖ f′)) ⊕ (b′ ⊗ (c′ ⊖ e′))
        ⊜
        ((a′ ⊗ d′) ⊕ (b′ ⊗ c′))
          ⊖ ((a′ ⊗ f′) ⊕ (b′ ⊗ e′)))
      BishopP.≃-refl a b c d e f)

-- (p*q)*u - q*v = q * (p*u - v).
originalBishopScaledStepDefectFactor :
  ∀ p q u v →
  Complex._≈C_
    (((p *C q) *C u) -C (q *C v))
    (q *C ((p *C u) -C v))
originalBishopScaledStepDefectFactor p q u v =
  complexTrans
    (Algebra.subCCongruent
      (complexTrans
        (Algebra.mulCCongruent
          (Laws.complexMultiplyCommutative p q)
          (Complex.≈C-refl u))
        (Laws.complexMultiplyAssociative q p u))
      (Complex.≈C-refl (q *C v)))
    (complexSym (complexMultiplyDifference q (p *C u) v))

-- Original endomap recursion was right-composed; this proves that its
-- left-composed formulation is the SAME sequence, not another orbit.
originalBishopInverseOrbitCommutes :
  ∀ g n z →
  g (Orbit.inverseOrbit g n z)
    ≡ Orbit.inverseOrbit g n (g z)
originalBishopInverseOrbitCommutes g zero z = refl
originalBishopInverseOrbitCommutes g (suc n) z =
  originalBishopInverseOrbitCommutes g n (g z)

originalBishopInverseOrbitNextIsImage :
  ∀ g n z →
  Orbit.inverseOrbit g (suc n) z
    ≡ g (Orbit.inverseOrbit g n z)
originalBishopInverseOrbitNextIsImage g n z =
  sym (originalBishopInverseOrbitCommutes g n z)

originalBishopLogLocalTaylorRemainder :
  (p : Complex.BishopComplex) →
  Reciprocal.BishopComplexNonzero p →
  (g : Complex.BishopComplex → Complex.BishopComplex) →
  Complex.BishopComplex → Complex.BishopComplex
originalBishopLogLocalTaylorRemainder p nz g w =
  ((g w) -C p) -C
    ((Reciprocal.reciprocalC p nz) *C (w -C p))

-- p * R_p(w) ≈ p*(g(w)-p) - (w-p).
originalBishopLogRemainderCancelsLinear :
  ∀ p (nz : Reciprocal.BishopComplexNonzero p) g w →
  Complex._≈C_
    (p *C (originalBishopLogLocalTaylorRemainder p nz g w))
    ((p *C ((g w) -C p)) -C (w -C p))
originalBishopLogRemainderCancelsLinear p nz g w =
  complexTrans
    (complexMultiplyDifference p
      ((g w) -C p)
      ((Reciprocal.reciprocalC p nz) *C (w -C p)))
    (Algebra.subCCongruent
      (Complex.≈C-refl (p *C ((g w) -C p)))
      (complexTrans
        (complexSym
          (Laws.complexMultiplyAssociative
            p (Reciprocal.reciprocalC p nz) (w -C p)))
        (complexTrans
          (Algebra.mulCCongruent
            (Reciprocal.multiplyReciprocal p nz)
            (Complex.≈C-refl (w -C p)))
          (Laws.complexMultiplyLeftIdentity (w -C p)))))

-- This is the same actual trajectory consumed by
-- AbelBishopInverseKoenigsGeometricOrbitExact.
originalBishopInverseKoenigsDifferenceIsScaledDefect :
  ∀ p g n z →
  Complex._≈C_
    (Telescope.originalBishopComplexStepDifference
      (λ k → Orbit.inverseKoenigsPrefix p g k z) n)
    ((powC p n) *C
      (((p *C ((g (Orbit.inverseOrbit g n z)) -C p))
         -C (Orbit.inverseOrbit g n z -C p))))
originalBishopInverseKoenigsDifferenceIsScaledDefect p g n z
  rewrite originalBishopInverseOrbitNextIsImage g n z =
  originalBishopScaledStepDefectFactor
    p (powC p n)
    ((g (Orbit.inverseOrbit g n z)) -C p)
    (Orbit.inverseOrbit g n z -C p)

originalBishopInverseKoenigsDifferenceIsScaledRemainder :
  ∀ p (nz : Reciprocal.BishopComplexNonzero p) g n z →
  Complex._≈C_
    (Telescope.originalBishopComplexStepDifference
      (λ k → Orbit.inverseKoenigsPrefix p g k z) n)
    ((powC p n) *C
      (p *C
        originalBishopLogLocalTaylorRemainder
          p nz g (Orbit.inverseOrbit g n z)))
originalBishopInverseKoenigsDifferenceIsScaledRemainder
  p nz g n z =
  complexTrans
    (originalBishopInverseKoenigsDifferenceIsScaledDefect p g n z)
    (Algebra.mulCCongruent
      (Complex.≈C-refl (powC p n))
      (complexSym
        (originalBishopLogRemainderCancelsLinear
          p nz g (Orbit.inverseOrbit g n z))))
