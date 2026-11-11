module DASHI.Moonshine.AbelBishopFactorialComplexImaginaryAxisTwoStepExact where

------------------------------------------------------------------------
-- ORIGINAL BISHOP COMPLEX: ALL-DEGREE IMAGINARY-AXIS TWO-STEP LAW.
--
-- For z = (0,y), the actual Cartesian multiplication gives
--       z * (z * q) ~= (-y*y) * q
-- for every original Bishop complex q. Consequently
--       z^(n+2) ~= (-y*y) * z^n
-- on the same source carrier, for every n. This is the finite
-- algebra needed to identify odd/even factorial terms with the
-- existing concrete Bishop sine/cosine term owners.
--
-- It does NOT assert an infinite sine/cosine limit identification,
-- expC equality, or an exp-log inverse; Agda acceptance pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Rational.Unnormalised using (0ℚᵘ)

import Real as BishopReal
import RealProperties as BishopP
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra

imaginaryAxis : BishopReal.ℝ → Complex.BishopComplex
imaginaryAxis y = Complex.complex BishopReal.0ℝ y

negativeSquare : BishopReal.ℝ → BishopReal.ℝ
negativeSquare y = BishopReal.- (BishopReal._*_ y y)

originalBishopImaginaryAxisDoubleMultiply :
  ∀ y q →
  Complex._≈C_
    (Algebra._*C_
      (imaginaryAxis y)
      (Algebra._*C_ (imaginaryAxis y) q))
    (Algebra.scaleC (negativeSquare y) q)
originalBishopImaginaryAxisDoubleMultiply
  y (Complex.complex a b) =
  (let open BishopP.ℝ-Solver in
   solve 3
     (λ y′ a′ b′ →
       ((Κ 0ℚᵘ ⊗
         ((Κ 0ℚᵘ ⊗ a′) ⊖ (y′ ⊗ b′)))
       ⊖
       (y′ ⊗
         ((Κ 0ℚᵘ ⊗ b′) ⊕ (y′ ⊗ a′))))
       ⊜ ((⊝ (y′ ⊗ y′)) ⊗ a′))
     BishopP.≃-refl y a b)
  ,
  (let open BishopP.ℝ-Solver in
   solve 3
     (λ y′ a′ b′ →
       ((Κ 0ℚᵘ ⊗
         ((Κ 0ℚᵘ ⊗ b′) ⊕ (y′ ⊗ a′)))
       ⊕
       (y′ ⊗
         ((Κ 0ℚᵘ ⊗ a′) ⊖ (y′ ⊗ b′))))
       ⊜ ((⊝ (y′ ⊗ y′)) ⊗ b′))
     BishopP.≃-refl y a b)

originalBishopImaginaryAxisPowerTwoStep :
  ∀ y n →
  Complex._≈C_
    (Algebra.powC (imaginaryAxis y) (suc (suc n)))
    (Algebra.scaleC
      (negativeSquare y)
      (Algebra.powC (imaginaryAxis y) n))
originalBishopImaginaryAxisPowerTwoStep y n =
  originalBishopImaginaryAxisDoubleMultiply
    y (Algebra.powC (imaginaryAxis y) n)

originalBishopImaginaryAxisPowerTwoStepReal :
  ∀ y n →
  BishopReal._≃_
    (Complex.re (Algebra.powC (imaginaryAxis y) (suc (suc n))))
    (BishopReal._*_
      (negativeSquare y)
      (Complex.re (Algebra.powC (imaginaryAxis y) n)))
originalBishopImaginaryAxisPowerTwoStepReal y n =
  proj₁ (originalBishopImaginaryAxisPowerTwoStep y n)

originalBishopImaginaryAxisPowerTwoStepImag :
  ∀ y n →
  BishopReal._≃_
    (Complex.im (Algebra.powC (imaginaryAxis y) (suc (suc n))))
    (BishopReal._*_
      (negativeSquare y)
      (Complex.im (Algebra.powC (imaginaryAxis y) n)))
originalBishopImaginaryAxisPowerTwoStepImag y n =
  proj₂ (originalBishopImaginaryAxisPowerTwoStep y n)
