module DASHI.Physics.Closure.NSTriadKNWaleffeHeronPolynomialRound102Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND102 / EXACT WALEFFE-HERON POLYNOMIAL
--
-- The geometric numerator in Waleffe's helical coupling is controlled by the
-- triangle-area polynomial
--
--   Q^2 = 2(k^2 p^2 + p^2 q^2 + q^2 k^2) - k^4 - p^4 - q^4.
--
-- This module proves, over the repository's arbitrary RealField carrier, the
-- exact Heron factorization
--
--   Q^2 = (k+p+q)(-k+p+q)(k-p+q)(k+p-q).
--
-- No square root, division, positivity, or analytic estimate is assumed.  The
-- factorization exposes the four triangle defects directly and is therefore
-- the right division-free bridge between literal triad geometry and the
-- Round102 minority-leg Waleffe bounds.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field

private
  sq : ∀ {r} {F : C3.RealField r} → C3.Carrier F → C3.Carrier F
  sq {F = F} x = C3.multiply F x x

  neg : ∀ {r} {F : C3.RealField r} → C3.Carrier F → C3.Carrier F
  neg {F = F} x = C3.negate F x

  add3 : ∀ {r} {F : C3.RealField r} →
    C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F
  add3 {F = F} x y z = C3.add F x (C3.add F y z)

waleffeAreaPolynomial :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F
waleffeAreaPolynomial {F = F} k p q =
  C3.add F
    (C3.multiply F
      (C3.add F (C3.one F) (C3.one F))
      (C3.add F
        (C3.multiply F (sq k) (sq p))
        (C3.add F
          (C3.multiply F (sq p) (sq q))
          (C3.multiply F (sq q) (sq k)))))
    (C3.negate F
      (C3.add F (sq (sq k))
        (C3.add F (sq (sq p)) (sq (sq q)))))

heronProduct :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F
heronProduct {F = F} k p q =
  C3.multiply F
    (add3 k p q)
    (C3.multiply F
      (add3 (neg k) p q)
      (C3.multiply F
        (add3 k (neg p) q)
        (add3 k p (neg q))))

waleffeAreaPolynomialIsHeronProduct :
  ∀ {r} {F : C3.RealField r} (k p q : C3.Carrier F) →
  waleffeAreaPolynomial k p q ≡ heronProduct k p q
waleffeAreaPolynomialIsHeronProduct {F = F} k p q =
  P.R.solve 3
    (λ k p q →
      (((P.R.K (C3.one F) P.R.⊕ P.R.K (C3.one F))
        P.R.⊗
        (((k P.R.⊗ k) P.R.⊗ (p P.R.⊗ p))
          P.R.⊕ (((p P.R.⊗ p) P.R.⊗ (q P.R.⊗ q))
          P.R.⊕ ((q P.R.⊗ q) P.R.⊗ (k P.R.⊗ k)))))
       P.R.⊕ P.R.⊝
        ((((k P.R.⊗ k) P.R.⊗ (k P.R.⊗ k))
          P.R.⊕ (((p P.R.⊗ p) P.R.⊗ (p P.R.⊗ p))
          P.R.⊕ ((q P.R.⊗ q) P.R.⊗ (q P.R.⊗ q))))))
      P.R.⊜
      ((k P.R.⊕ (p P.R.⊕ q))
        P.R.⊗ (((P.R.⊝ k) P.R.⊕ (p P.R.⊕ q))
        P.R.⊗ ((k P.R.⊕ ((P.R.⊝ p) P.R.⊕ q))
        P.R.⊗ (k P.R.⊕ (p P.R.⊕ (P.R.⊝ q)))))))
    refl k p q
  where module P = Field.Polynomial F

round102WaleffeHeronPolynomialFactorizationClosed : Bool
round102WaleffeHeronPolynomialFactorizationClosed = true

round102WaleffeHeronPolynomialFactorizationClosedIsTrue :
  round102WaleffeHeronPolynomialFactorizationClosed ≡ true
round102WaleffeHeronPolynomialFactorizationClosedIsTrue = refl
