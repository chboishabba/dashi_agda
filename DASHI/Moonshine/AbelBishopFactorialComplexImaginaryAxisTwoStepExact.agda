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
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as Estimates
import DASHI.Moonshine.AbelBishopFactorialComplexRealAxisTermsExact as FactorialTerms
import DASHI.Moonshine.AbelBishopFactorialComplexExpDiskExact as Factorial

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


------------------------------------------------------------------------
-- THE ORIGINAL YANG--MILLS SINE/COSINE INDEX CONVENTIONS ARE REUSED:
-- evenExponent k = 2k, oddExponent k = 2k+1.
-- The output powers here are (-y²)^k; the final parity/sign weld to
-- concrete sine/cosine signed factorial coefficients is still separate.
------------------------------------------------------------------------

originalBishopImaginaryAxisEvenPower :
  ∀ y n →
  Complex._≈C_
    (Algebra.powC
      (imaginaryAxis y)
      (Estimates.evenExponent n))
    (Complex.complex
      (BishopReal.pow (negativeSquare y) n)
      BishopReal.0ℝ)
originalBishopImaginaryAxisEvenPower y zero =
  (let open BishopP.ℝ-Solver in
   solve 0 (Κ 1ℚᵘ ⊜ Κ 1ℚᵘ) BishopP.≃-refl)
  ,
  (let open BishopP.ℝ-Solver in
   solve 0 (Κ 0ℚᵘ ⊜ Κ 0ℚᵘ) BishopP.≃-refl)
originalBishopImaginaryAxisEvenPower y (suc n) =
  let
    u = negativeSquare y
    p = BishopReal.pow u n
    previous = originalBishopImaginaryAxisEvenPower y n
    step = originalBishopImaginaryAxisPowerTwoStep y
      (Estimates.evenExponent n)
    substituted = Algebra.scaleCCongruent previous u
    realTail :
      BishopReal._≃_
        (BishopReal._*_ u p)
        (BishopReal.pow u (suc n))
    realTail =
      let open BishopP.ℝ-Solver in
      solve 2
        (λ u′ p′ → u′ ⊗ p′ ⊜ p′ ⊗ u′)
        BishopP.≃-refl u p
    imagTail :
      BishopReal._≃_
        (BishopReal._*_ u BishopReal.0ℝ)
        BishopReal.0ℝ
    imagTail =
      let open BishopP.ℝ-Solver in
      solve 1
        (λ u′ → u′ ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ)
        BishopP.≃-refl u
  in
  (BishopP.≃-trans (proj₁ step)
    (BishopP.≃-trans (proj₁ substituted) realTail))
  ,
  (BishopP.≃-trans (proj₂ step)
    (BishopP.≃-trans (proj₂ substituted) imagTail))

originalBishopImaginaryAxisOddPower :
  ∀ y n →
  Complex._≈C_
    (Algebra.powC
      (imaginaryAxis y)
      (Estimates.oddExponent n))
    (Complex.complex
      BishopReal.0ℝ
      (BishopReal._*_ y (BishopReal.pow (negativeSquare y) n)))
originalBishopImaginaryAxisOddPower y zero =
  (let open BishopP.ℝ-Solver in
   solve 1
     (λ y′ →
       ((Κ 0ℚᵘ ⊗ Κ 1ℚᵘ) ⊖ (y′ ⊗ Κ 0ℚᵘ))
       ⊜ Κ 0ℚᵘ)
     BishopP.≃-refl y)
  ,
  (let open BishopP.ℝ-Solver in
   solve 1
     (λ y′ →
       ((Κ 0ℚᵘ ⊗ Κ 0ℚᵘ) ⊕ (y′ ⊗ Κ 1ℚᵘ))
       ⊜ (y′ ⊗ Κ 1ℚᵘ))
     BishopP.≃-refl y)
originalBishopImaginaryAxisOddPower y (suc n) =
  let
    u = negativeSquare y
    p = BishopReal.pow u n
    yp = BishopReal._*_ y p
    previous = originalBishopImaginaryAxisOddPower y n
    step = originalBishopImaginaryAxisPowerTwoStep y
      (Estimates.oddExponent n)
    substituted = Algebra.scaleCCongruent previous u
    realTail :
      BishopReal._≃_
        (BishopReal._*_ u BishopReal.0ℝ)
        BishopReal.0ℝ
    realTail =
      let open BishopP.ℝ-Solver in
      solve 1
        (λ u′ → u′ ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ)
        BishopP.≃-refl u
    imagTail :
      BishopReal._≃_
        (BishopReal._*_ u yp)
        (BishopReal._*_ y (BishopReal.pow u (suc n)))
    imagTail =
      let open BishopP.ℝ-Solver in
      solve 3
        (λ u′ y′ p′ →
          u′ ⊗ (y′ ⊗ p′)
          ⊜ y′ ⊗ (p′ ⊗ u′))
        BishopP.≃-refl u y p
  in
  (BishopP.≃-trans (proj₁ step)
    (BishopP.≃-trans (proj₁ substituted) realTail))
  ,
  (BishopP.≃-trans (proj₂ step)
    (BishopP.≃-trans (proj₂ substituted) imagTail))


------------------------------------------------------------------------
-- INSTANTIATION ON THE EXACT COMPLEX FACTORIAL SOURCE TERMS.
-- They are the same terms as the real-axis owner, not a new series.
------------------------------------------------------------------------

originalBishopImaginaryAxisFactorialEvenTerm :
  ∀ y n →
  Complex._≈C_
    (FactorialTerms.originalBishopFactorialComplexTerm
      (imaginaryAxis y)
      (Estimates.evenExponent n))
    (Complex.complex
      (BishopReal._*_
        (Factorial.factorialCoefficient (Estimates.evenExponent n))
        (BishopReal.pow (negativeSquare y) n))
      BishopReal.0ℝ)
originalBishopImaginaryAxisFactorialEvenTerm y n =
  let
    coeff = Factorial.factorialCoefficient (Estimates.evenExponent n)
    power = originalBishopImaginaryAxisEvenPower y n
  in
  (BishopP.*-congˡ (proj₁ power))
  ,
  (BishopP.≃-trans
    (BishopP.*-congˡ (proj₂ power))
    (let open BishopP.ℝ-Solver in
     solve 1
       (λ c → c ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ)
       BishopP.≃-refl coeff))

originalBishopImaginaryAxisFactorialOddTerm :
  ∀ y n →
  Complex._≈C_
    (FactorialTerms.originalBishopFactorialComplexTerm
      (imaginaryAxis y)
      (Estimates.oddExponent n))
    (Complex.complex
      BishopReal.0ℝ
      (BishopReal._*_
        (Factorial.factorialCoefficient (Estimates.oddExponent n))
        (BishopReal._*_ y (BishopReal.pow (negativeSquare y) n))))
originalBishopImaginaryAxisFactorialOddTerm y n =
  let
    coeff = Factorial.factorialCoefficient (Estimates.oddExponent n)
    power = originalBishopImaginaryAxisOddPower y n
  in
  (BishopP.≃-trans
    (BishopP.*-congˡ (proj₁ power))
    (let open BishopP.ℝ-Solver in
     solve 1
       (λ c → c ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ)
       BishopP.≃-refl coeff))
  ,
  (BishopP.*-congˡ (proj₂ power))
