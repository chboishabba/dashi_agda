module DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact where

------------------------------------------------------------------------
-- ORIGINAL BISHOP-COMPLEX COMMUTATIVE-SEMIRING LAWS.
--
-- This is the exact Cartesian pair carrier used by the original
-- factorial and Cauchy series. All proofs are per-coordinate uses
-- of the already-proved Bishop-real commutative ring and its solver.
--
-- These are the law inputs for a future actual stdlib
-- CommutativeSemiring bundle/binomial instance. No surrogate complex
-- type, postulate, or unproved binomial theorem is introduced.
------------------------------------------------------------------------

import Real as BishopReal
import RealProperties as BishopP
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
open import Data.Product.Base using (_,_)

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra

complexAddAssociative :
  ∀ x y z →
  Complex._≈C_
    (Algebra._+C_ (Algebra._+C_ x y) z)
    (Algebra._+C_ x (Algebra._+C_ y z))
complexAddAssociative
  (Complex.complex a b)
  (Complex.complex c d)
  (Complex.complex e f) =
  BishopP.+-assoc a c e
  ,
  BishopP.+-assoc b d f

complexAddCommutative :
  ∀ x y →
  Complex._≈C_ (Algebra._+C_ x y) (Algebra._+C_ y x)
complexAddCommutative
  (Complex.complex a b) (Complex.complex c d) =
  BishopP.+-comm a c , BishopP.+-comm b d

complexAddLeftIdentity :
  ∀ x → Complex._≈C_ (Algebra._+C_ Algebra.zeroC x) x
complexAddLeftIdentity (Complex.complex a b) =
  BishopP.+-identityˡ a , BishopP.+-identityˡ b

complexAddRightIdentity :
  ∀ x → Complex._≈C_ (Algebra._+C_ x Algebra.zeroC) x
complexAddRightIdentity (Complex.complex a b) =
  BishopP.+-identityʳ a , BishopP.+-identityʳ b

complexMultiplyCommutative :
  ∀ x y →
  Complex._≈C_ (Algebra._*C_ x y) (Algebra._*C_ y x)
complexMultiplyCommutative
  (Complex.complex a b) (Complex.complex c d) =
  (let open BishopP.ℝ-Solver in
    solve 4
      (λ a′ b′ c′ d′ →
        ((a′ ⊗ c′) ⊖ (b′ ⊗ d′))
        ⊜ ((c′ ⊗ a′) ⊖ (d′ ⊗ b′)))
      BishopP.≃-refl a b c d)
  ,
  (let open BishopP.ℝ-Solver in
    solve 4
      (λ a′ b′ c′ d′ →
        ((a′ ⊗ d′) ⊕ (b′ ⊗ c′))
        ⊜ ((c′ ⊗ b′) ⊕ (d′ ⊗ a′)))
      BishopP.≃-refl a b c d)

complexMultiplyAssociative :
  ∀ x y z →
  Complex._≈C_
    (Algebra._*C_ (Algebra._*C_ x y) z)
    (Algebra._*C_ x (Algebra._*C_ y z))
complexMultiplyAssociative
  (Complex.complex a b)
  (Complex.complex c d)
  (Complex.complex e f) =
  (let open BishopP.ℝ-Solver in
    solve 6
      (λ a′ b′ c′ d′ e′ f′ →
        (((a′ ⊗ c′) ⊖ (b′ ⊗ d′)) ⊗ e′)
          ⊖ (((a′ ⊗ d′) ⊕ (b′ ⊗ c′)) ⊗ f′)
        ⊜
        (a′ ⊗ ((c′ ⊗ e′) ⊖ (d′ ⊗ f′)))
          ⊖ (b′ ⊗ ((c′ ⊗ f′) ⊕ (d′ ⊗ e′))))
      BishopP.≃-refl a b c d e f)
  ,
  (let open BishopP.ℝ-Solver in
    solve 6
      (λ a′ b′ c′ d′ e′ f′ →
        (((a′ ⊗ c′) ⊖ (b′ ⊗ d′)) ⊗ f′)
          ⊕ (((a′ ⊗ d′) ⊕ (b′ ⊗ c′)) ⊗ e′)
        ⊜
        (a′ ⊗ ((c′ ⊗ f′) ⊕ (d′ ⊗ e′)))
          ⊕ (b′ ⊗ ((c′ ⊗ e′) ⊖ (d′ ⊗ f′))))
      BishopP.≃-refl a b c d e f)

complexMultiplyLeftIdentity :
  ∀ x → Complex._≈C_ (Algebra._*C_ Algebra.oneC x) x
complexMultiplyLeftIdentity (Complex.complex a b) =
  (let open BishopP.ℝ-Solver in
   solve 2
     (λ a′ b′ →
       (Κ 1ℚᵘ ⊗ a′) ⊖ (Κ 0ℚᵘ ⊗ b′) ⊜ a′)
     BishopP.≃-refl a b)
  ,
  (let open BishopP.ℝ-Solver in
   solve 2
     (λ a′ b′ →
       (Κ 1ℚᵘ ⊗ b′) ⊕ (Κ 0ℚᵘ ⊗ a′) ⊜ b′)
     BishopP.≃-refl a b)

complexMultiplyRightIdentity :
  ∀ x → Complex._≈C_ (Algebra._*C_ x Algebra.oneC) x
complexMultiplyRightIdentity (Complex.complex a b) =
  (let open BishopP.ℝ-Solver in
   solve 2
     (λ a′ b′ →
       (a′ ⊗ Κ 1ℚᵘ) ⊖ (b′ ⊗ Κ 0ℚᵘ) ⊜ a′)
     BishopP.≃-refl a b)
  ,
  (let open BishopP.ℝ-Solver in
   solve 2
     (λ a′ b′ →
       (a′ ⊗ Κ 0ℚᵘ) ⊕ (b′ ⊗ Κ 1ℚᵘ) ⊜ b′)
     BishopP.≃-refl a b)

complexMultiplyLeftZero :
  ∀ x → Complex._≈C_ (Algebra._*C_ Algebra.zeroC x) Algebra.zeroC
complexMultiplyLeftZero (Complex.complex a b) =
  (let open BishopP.ℝ-Solver in
   solve 2
     (λ a′ b′ →
       (Κ 0ℚᵘ ⊗ a′) ⊖ (Κ 0ℚᵘ ⊗ b′) ⊜ Κ 0ℚᵘ)
     BishopP.≃-refl a b)
  ,
  (let open BishopP.ℝ-Solver in
   solve 2
     (λ a′ b′ →
       (Κ 0ℚᵘ ⊗ b′) ⊕ (Κ 0ℚᵘ ⊗ a′) ⊜ Κ 0ℚᵘ)
     BishopP.≃-refl a b)

complexMultiplyRightZero :
  ∀ x → Complex._≈C_ (Algebra._*C_ x Algebra.zeroC) Algebra.zeroC
complexMultiplyRightZero (Complex.complex a b) =
  (let open BishopP.ℝ-Solver in
   solve 2
     (λ a′ b′ →
       (a′ ⊗ Κ 0ℚᵘ) ⊖ (b′ ⊗ Κ 0ℚᵘ) ⊜ Κ 0ℚᵘ)
     BishopP.≃-refl a b)
  ,
  (let open BishopP.ℝ-Solver in
   solve 2
     (λ a′ b′ →
       (a′ ⊗ Κ 0ℚᵘ) ⊕ (b′ ⊗ Κ 0ℚᵘ) ⊜ Κ 0ℚᵘ)
     BishopP.≃-refl a b)

complexMultiplyDistributesLeft :
  ∀ x y z →
  Complex._≈C_
    (Algebra._*C_ x (Algebra._+C_ y z))
    (Algebra._+C_
      (Algebra._*C_ x y) (Algebra._*C_ x z))
complexMultiplyDistributesLeft
  (Complex.complex a b)
  (Complex.complex c d)
  (Complex.complex e f) =
  (let open BishopP.ℝ-Solver in
   solve 6
     (λ a′ b′ c′ d′ e′ f′ →
       (a′ ⊗ (c′ ⊕ e′)) ⊖ (b′ ⊗ (d′ ⊕ f′))
       ⊜
       ((a′ ⊗ c′) ⊖ (b′ ⊗ d′))
         ⊕ ((a′ ⊗ e′) ⊖ (b′ ⊗ f′)))
     BishopP.≃-refl a b c d e f)
  ,
  (let open BishopP.ℝ-Solver in
   solve 6
     (λ a′ b′ c′ d′ e′ f′ →
       (a′ ⊗ (d′ ⊕ f′)) ⊕ (b′ ⊗ (c′ ⊕ e′))
       ⊜
       ((a′ ⊗ d′) ⊕ (b′ ⊗ c′))
         ⊕ ((a′ ⊗ f′) ⊕ (b′ ⊗ e′)))
     BishopP.≃-refl a b c d e f)

complexMultiplyDistributesRight :
  ∀ x y z →
  Complex._≈C_
    (Algebra._*C_ (Algebra._+C_ x y) z)
    (Algebra._+C_
      (Algebra._*C_ x z) (Algebra._*C_ y z))
complexMultiplyDistributesRight
  (Complex.complex a b)
  (Complex.complex c d)
  (Complex.complex e f) =
  (let open BishopP.ℝ-Solver in
   solve 6
     (λ a′ b′ c′ d′ e′ f′ →
       ((a′ ⊕ c′) ⊗ e′) ⊖ ((b′ ⊕ d′) ⊗ f′)
       ⊜
       ((a′ ⊗ e′) ⊖ (b′ ⊗ f′))
         ⊕ ((c′ ⊗ e′) ⊖ (d′ ⊗ f′)))
     BishopP.≃-refl a b c d e f)
  ,
  (let open BishopP.ℝ-Solver in
   solve 6
     (λ a′ b′ c′ d′ e′ f′ →
       ((a′ ⊕ c′) ⊗ f′) ⊕ ((b′ ⊕ d′) ⊗ e′)
       ⊜
       ((a′ ⊗ f′) ⊕ (b′ ⊗ e′))
         ⊕ ((c′ ⊗ f′) ⊕ (d′ ⊗ e′)))
     BishopP.≃-refl a b c d e f)
