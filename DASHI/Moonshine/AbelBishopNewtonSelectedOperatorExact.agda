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


------------------------------------------------------------------------
-- CONVERSE: same-source Newton fixed point => native exp fixed point.
-- This uses the exact Bishop reciprocal of expC(p0)-1 and the
-- cancellative complex ring, NOT a classical inverse function axiom.
------------------------------------------------------------------------

complexSubtractCancellation :
  ∀ x error →
  Complex._≈C_ (x -C error) x →
  Complex._≈C_ error Algebra.zeroC
complexSubtractCancellation
  (Complex.complex a b) (Complex.complex c d) fixed =
  let
    recover :
      Complex._≈C_
        ((Complex.complex a b)
          -C ((Complex.complex a b) -C (Complex.complex c d)))
        (Complex.complex c d)
    recover =
      (let open BishopP.ℝ-Solver in
        solve 2
          (λ x y → x ⊖ (x ⊖ y) ⊜ y)
          BishopP.≃-refl a c)
      ,
      (let open BishopP.ℝ-Solver in
        solve 2
          (λ x y → x ⊖ (x ⊖ y) ⊜ y)
          BishopP.≃-refl b d)
  in
  Ring.complexTrans
    (Ring.complexSym recover)
    (Ring.complexTrans
      (Algebra.subCCongruent
        (Complex.≈C-refl (Complex.complex a b))
        fixed)
      (Orbit.complexSubtractSelfZero (Complex.complex a b)))

complexDefectPlusArgument :
  ∀ expValue z →
  Complex._≈C_
    (Algebra._+C_ (expValue -C z) z)
    expValue
complexDefectPlusArgument
  (Complex.complex a b) (Complex.complex c d) =
  (let open BishopP.ℝ-Solver in
    solve 2
      (λ e z → (e ⊖ z) ⊕ z ⊜ e)
      BishopP.≃-refl a c)
  ,
  (let open BishopP.ℝ-Solver in
    solve 2
      (λ e z → (e ⊖ z) ⊕ z ⊜ e)
      BishopP.≃-refl b d)

originalBishopNewtonOperatorFixedImpliesExpFixed :
  ∀ T nonzero z →
  Complex._≈C_ (originalBishopNewtonOperator T nonzero z) z →
  Complex._≈C_ (Native.originalBishopExpOnSeries T z) z
originalBishopNewtonOperatorFixedImpliesExpFixed T nonzero z fixed =
  let
    expValue = Native.originalBishopExpOnSeries T z
    f = originalBishopExponentialDefect T z
    denominator = originalBishopNewtonDenominator T
    inverse = Reciprocal.reciprocalC denominator nonzero
    error = f *C inverse

    errorZero : Complex._≈C_ error Algebra.zeroC
    errorZero = complexSubtractCancellation z error fixed

    reciprocalLeft :
      Complex._≈C_ (inverse *C denominator) Algebra.oneC
    reciprocalLeft =
      Ring.complexTrans
        (Laws.complexMultiplyCommutative inverse denominator)
        (Reciprocal.multiplyReciprocal denominator nonzero)

    multiplicationCancels :
      Complex._≈C_ ((f *C inverse) *C denominator) f
    multiplicationCancels =
      Ring.complexTrans
        (Laws.complexMultiplyAssociative f inverse denominator)
        (Ring.complexTrans
          (Algebra.mulCCongruent
            (Complex.≈C-refl f)
            reciprocalLeft)
          (Laws.complexMultiplyRightIdentity f))

    fZero : Complex._≈C_ f Algebra.zeroC
    fZero =
      Ring.complexTrans
        (Ring.complexSym multiplicationCancels)
        (Ring.complexTrans
          (Algebra.mulCCongruent
            errorZero
            (Complex.≈C-refl denominator))
          (Laws.complexMultiplyLeftZero denominator))
  in
  Ring.complexTrans
    (Ring.complexSym (complexDefectPlusArgument expValue z))
    (Ring.complexTrans
      (Algebra.addCCongruent
        fZero
        (Complex.≈C-refl z))
      (Laws.complexAddLeftIdentity z))
