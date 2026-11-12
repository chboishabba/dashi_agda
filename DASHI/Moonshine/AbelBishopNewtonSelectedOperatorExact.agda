module DASHI.Moonshine.AbelBishopNewtonSelectedOperatorExact where

------------------------------------------------------------------------
-- EXACT NEWTON ITERATION ON THE ORIGINAL BISHOP COMPLEX EXPONENTIAL.
--
-- p0 = 31813/100000 + i 133724/100000, embedded into the literal
-- BishopComplexSeriesConvergenceExact carrier (not a decimal Float).
--
-- T(z) = z - (expC(z)-z) * (expC(p0)-1)^-1.
--
-- The original BishopComplexReciprocalExact supplies the SAME
-- denominator reciprocal, under its actual positive norm-square proof.
-- This module does not assume the denominator is nonzero; it keeps the
-- explicit original positive norm-square certificate as a parameter.
--
-- Actual Newton iteration is a concrete Nat-recursive source stream,
-- suitable for later Bishop Cauchy completion. We prove the finite
-- fixed-point compatibility from original ring laws. No Banach axiom,
-- classical choice, fake contraction constant or hidden surrogate exp.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
open import Data.Product.Base using (_,_; proj₁; proj₂)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexReciprocalExact as Reciprocal
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as Laws
import DASHI.Analysis.BishopSetoidComplexExact as Cartesian
import DASHI.Moonshine.AbelBishopOriginalComplexCarrierWeldExact as Native
import DASHI.Moonshine.AbelBishopInverseKoenigsFiniteOrbitExact as Orbit
import DASHI.Moonshine.AbelBishopInverseKoenigsRemainderFactorExact as Ring

open Algebra using (_-C_; _*C_)

selectedRationalNewtonCenter : Complex.BishopComplex
selectedRationalNewtonCenter =
  Complex.complex
    (BishopReal._⋆ (+ 31813 / 100000))
    (BishopReal._⋆ (+ 133724 / 100000))

originalBishopExponentialDefect :
  Cartesian.BishopSetoidComplexTranscendentals →
  Complex.BishopComplex → Complex.BishopComplex
originalBishopExponentialDefect T z =
  (Native.originalBishopExpOnSeries T z) -C z

originalBishopNewtonDenominator :
  Cartesian.BishopSetoidComplexTranscendentals →
  Complex.BishopComplex
originalBishopNewtonDenominator T =
  (Native.originalBishopExpOnSeries T selectedRationalNewtonCenter)
    -C Algebra.oneC

originalBishopNewtonOperator :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  Reciprocal.BishopComplexNonzero
    (originalBishopNewtonDenominator T) →
  Complex.BishopComplex → Complex.BishopComplex
originalBishopNewtonOperator T nonzero z =
  z -C
    ((originalBishopExponentialDefect T z) *C
      (Reciprocal.reciprocalC
        (originalBishopNewtonDenominator T) nonzero))

originalBishopNewtonOrbit :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  (nonzero : Reciprocal.BishopComplexNonzero
    (originalBishopNewtonDenominator T)) →
  Nat → Complex.BishopComplex
originalBishopNewtonOrbit T nonzero zero =
  selectedRationalNewtonCenter
originalBishopNewtonOrbit T nonzero (suc n) =
  originalBishopNewtonOperator T nonzero
    (originalBishopNewtonOrbit T nonzero n)

originalBishopNewtonOrbitStartsAtSelectedCenter :
  ∀ T nonzero →
  originalBishopNewtonOrbit T nonzero zero
    ≡ selectedRationalNewtonCenter
originalBishopNewtonOrbitStartsAtSelectedCenter T nonzero = refl

originalBishopNewtonOrbitIsActualIteration :
  ∀ T nonzero n →
  originalBishopNewtonOrbit T nonzero (suc n)
    ≡ originalBishopNewtonOperator T nonzero
        (originalBishopNewtonOrbit T nonzero n)
originalBishopNewtonOrbitIsActualIteration T nonzero n = refl

complexSubtractZero :
  ∀ z →
  Complex._≈C_ (z -C Algebra.zeroC) z
complexSubtractZero (Complex.complex a b) =
  (let open BishopP.ℝ-Solver in
    solve 1 (λ x → x ⊖ Κ (+ 0 / 1) ⊜ x)
      BishopP.≃-refl a)
  ,
  (let open BishopP.ℝ-Solver in
    solve 1 (λ x → x ⊖ Κ (+ 0 / 1) ⊜ x)
      BishopP.≃-refl b)

-- A true source fixed point of native expC is indeed a fixed point of
-- this exact Newton map. The converse / EXISTENCE requires separate
-- constructive Newton orbit convergence and source continuity.
originalBishopExpFixedPointIsNewtonFixedPoint :
  ∀ T nonzero z →
  Complex._≈C_
    (Native.originalBishopExpOnSeries T z)
    z →
  Complex._≈C_
    (originalBishopNewtonOperator T nonzero z)
    z
originalBishopExpFixedPointIsNewtonFixedPoint T nonzero z fixed =
  Ring.complexTrans
    (Algebra.subCCongruent
      (Complex.≈C-refl z)
      (Ring.complexTrans
        (Algebra.mulCCongruent
          (Ring.complexTrans
            (Algebra.subCCongruent
              fixed
              (Complex.≈C-refl z))
            (Orbit.complexSubtractSelfZero z))
          (Complex.≈C-refl
            (Reciprocal.reciprocalC
              (originalBishopNewtonDenominator T) nonzero)))
        (Laws.complexMultiplyLeftZero
          (Reciprocal.reciprocalC
            (originalBishopNewtonDenominator T) nonzero))))
    (complexSubtractZero z)
