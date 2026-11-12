module DASHI.Analysis.BishopOriginalXiPolynomialReflectionSameCarrierExact where

------------------------------------------------------------------------
-- P3: ORIGINAL BISHOP COMPLEX (not only Q[i]) functional reflection.
--
-- The finite xi prefactor s(s-1) is invariant under s |-> 1-s
-- on the ACTUAL pinned Bishop ℝ Cartesian complex carrier.
-- The proof is in the source's componentwise Bishop SETOID.
--
-- Given a separately constructed symmetric Mellin tail T(s),
-- the normalized algebraic expression
--
--   X_T(s) = 1/2 + (1/2)*s(s-1)*T(s)
--
-- has the original functional reflection symmetry.
--
-- This is NOT a Gamma construction, theta Poisson transform,
-- entireness proof, order-one growth proof, analytic zeta
-- continuation or same-object xi identification.
------------------------------------------------------------------------

open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using
  (0ℚᵘ; 1ℚᵘ; _/_)

import Real as R
import RealProperties as RP
import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as BC
import DASHI.Analysis.BishopOriginalDirichletEtaFinitePairingExact as Native

complexRefl : (value : BC.BishopComplex) → Native._≈C_ value value
complexRefl value = RP.≃-refl , RP.≃-refl

complexMultiplyCongruent :
  ∀ {left left' right right' : BC.BishopComplex} →
  Native._≈C_ left left' →
  Native._≈C_ right right' →
  Native._≈C_ (BC._*C_ left right) (BC._*C_ left' right')
complexMultiplyCongruent leftEq rightEq =
  RP.+-cong
    (RP.*-cong (proj₁ leftEq) (proj₁ rightEq))
    (RP.-‿cong
      (RP.*-cong (proj₂ leftEq) (proj₂ rightEq)))
  ,
  RP.+-cong
    (RP.*-cong (proj₁ leftEq) (proj₂ rightEq))
    (RP.*-cong (proj₂ leftEq) (proj₁ rightEq))

complexAddLeftCongruent :
  (fixed : BC.BishopComplex) →
  ∀ {left right} →
  Native._≈C_ left right →
  Native._≈C_ (BC._+C_ fixed left) (BC._+C_ fixed right)
complexAddLeftCongruent fixed eq =
  RP.+-cong RP.≃-refl (proj₁ eq)
  ,
  RP.+-cong RP.≃-refl (proj₂ eq)

-- Same physical two-coordinate source as the existing
-- RiemannBishopComplexAnalyticCarrierExact, not the
-- independent rational RiemannXiSymmetryExact proxy.
bishopFunctionalReflection : BC.BishopComplex → BC.BishopComplex
bishopFunctionalReflection (BC.bishop-complex sigma tau) =
  BC.bishop-complex
    (R._-_ R.1ℝ sigma)
    (R.-_ tau)

bishopXiPolynomial : BC.BishopComplex → BC.BishopComplex
bishopXiPolynomial s =
  BC._*C_ s (BC._+C_ s (BC.negC BC.oneC))

originalBishopXiPolynomialReflection :
  (s : BC.BishopComplex) →
  Native._≈C_
    (bishopXiPolynomial s)
    (bishopXiPolynomial (bishopFunctionalReflection s))
originalBishopXiPolynomialReflection (BC.bishop-complex x y) =
  (let open RP.ℝ-Solver in
   solve 2
     (λ a b →
        (a ⊗ (a ⊕ (⊝ (Κ 1ℚᵘ))))
        ⊖ (b ⊗ (b ⊕ (⊝ (Κ 0ℚᵘ))))
        ⊜
        ((Κ 1ℚᵘ ⊖ a)
          ⊗ ((Κ 1ℚᵘ ⊖ a) ⊕ (⊝ (Κ 1ℚᵘ))))
        ⊖ ((⊝ b) ⊗ ((⊝ b) ⊕ (⊝ (Κ 0ℚᵘ)))))
     RP.≃-refl x y)
  ,
  (let open RP.ℝ-Solver in
   solve 2
     (λ a b →
       (a ⊗ (b ⊕ (⊝ (Κ 0ℚᵘ))))
         ⊕ (b ⊗ (a ⊕ (⊝ (Κ 1ℚᵘ))))
       ⊜
       ((Κ 1ℚᵘ ⊖ a)
          ⊗ ((⊝ b) ⊕ (⊝ (Κ 0ℚᵘ))))
         ⊕ ((⊝ b)
              ⊗ ((Κ 1ℚᵘ ⊖ a) ⊕ (⊝ (Κ 1ℚᵘ)))))
     RP.≃-refl x y)

bishopHalf : BC.BishopComplex
bishopHalf = BC.bishop-complex (R._⋆ (+ 1 / 2)) R.0ℝ

normalizedMellinExpression :
  (BC.BishopComplex → BC.BishopComplex) →
  BC.BishopComplex → BC.BishopComplex
normalizedMellinExpression tail s =
  BC._+C_ bishopHalf
    (BC._*C_ bishopHalf
      (BC._*C_ (bishopXiPolynomial s) (tail s)))

-- Actual COMPLETED-XI algebraic symmetry on the ORIGINAL
-- Bishop carrier, provided an original theta/Mellin analytic
-- producer later supplies its own source tail symmetry.
originalBishopNormalizedMellinSymmetry :
  (tail : BC.BishopComplex → BC.BishopComplex) →
  ((s : BC.BishopComplex) →
    Native._≈C_ (tail s) (tail (bishopFunctionalReflection s))) →
  (s : BC.BishopComplex) →
  Native._≈C_
    (normalizedMellinExpression tail s)
    (normalizedMellinExpression tail (bishopFunctionalReflection s))
originalBishopNormalizedMellinSymmetry tail tailSym s =
  complexAddLeftCongruent bishopHalf
    (complexMultiplyCongruent
      (complexRefl bishopHalf)
      (complexMultiplyCongruent
        (originalBishopXiPolynomialReflection s)
        (tailSym s)))

-- Remaining P3: construct an original Bishop-valued,
-- convergent, holomorphic Mellin tail T from the actual
-- Jacobi theta series; prove modular inversion and equality
-- to original zeta*Gamma completion; prove entireness/order.
-- This module explicitly does NOT instantiate that data.
