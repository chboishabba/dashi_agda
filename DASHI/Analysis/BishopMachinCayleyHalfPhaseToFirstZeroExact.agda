{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopMachinCayleyHalfPhaseToFirstZeroExact where

------------------------------------------------------------------------
-- K05-PI: REVERSE THE EXISTING MACHIN HALF-PHASE DEPENDENCY.
--
-- Previously the original Round11 first-zero consumer required a free
-- assertion cos_B(theta_M) ~= sin_B(theta_M).
--
-- The selected Cayley route supplies the stronger, more concrete target
--     exp_C(2*i*theta_M) ~= i
-- from original atan_B(1/5), atan_B(1/239) source evaluations plus
-- original imaginary exponential multiplication.
--
-- Here that *single selected original phase equation* replaces the
-- standalone quarter-angle premise. On the selected Round11 sine/cosine
-- series, the existing imaginary product gives:
--   sin_B(2theta_M) ~= 1
--   cos_B(theta_M)^2 + sin_B(theta_M)^2 ~= 1.
--
-- Native Bishop algebra then implies (cos_B theta_M - sin_B theta_M)^2=0;
-- the new square-zero theorem reflects it to setoid equality, WITHOUT
-- needing an unspecified real square-root calculus.
--
-- The established global two-ball sine sign theorem subsequently yields
-- pi_M as the FIRST positive original Bishop sine zero.
--
-- This module does not manufacture the half-phase equality. The only
-- independent K05-PI analytic input is the *source-owned*
-- arctangent-series/Cayley evaluation at the two Machin arguments;
-- the product law remains the already-owned K05-PRODUCT leaf.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ; _/_)

import Real as R
import RealProperties as RP

import DASHI.Analysis.BishopSetoidComplexExact as C
import DASHI.Analysis.BishopMachinQuarterPhaseQuadruplicationAlgebraExact as Quad
import DASHI.Analysis.BishopRound11ImaginaryProductPythagoreanReuseExact as Product
import DASHI.Analysis.BishopSquareZeroReflectsSetoidZeroExact as SquareZero
import DASHI.Analysis.BishopMachinPiGlobalSineSignFromTwoBallExact as Global
import DASHI.Analysis.BishopMachinFirstPositiveSineZeroFromNativePhaseExact as First
import DASHI.Foundations.BishopMachinQuarterAngleBranchExact as Quarter
import DASHI.Moonshine.BishopRound11MachinSetoidComplexInstanceExact as Route
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

-- This is a concrete equality between the ACTUAL original Bishop
-- signed-factorial exponential and the actual selected imaginary unit.
-- It is not an abstract "Pi is the correct number" authority.
OriginalMachinCayleyHalfPhase :
  Round11.Round11BishopCutset → Set
OriginalMachinCayleyHalfPhase inputs =
  C._≈C_
    (C.expC
      (Route.round11MachinTranscendentals inputs)
      (C.pureImaginary Quad.twiceQuarter))
    C.imaginaryUnit

sourceMachinHalfSineIsOneFromCayley :
  (inputs : Round11.Round11BishopCutset) →
  OriginalMachinCayleyHalfPhase inputs →
  R._≃_
    (Quad.round11Sine inputs Quad.twiceQuarter)
    R.1ℝ
sourceMachinHalfSineIsOneFromCayley inputs selectedCayley =
  C.imEquivalent
    (C.≈C-trans
      (C.≈C-sym
        (C.imaginaryExponentialIsPhase
          (Route.round11MachinTranscendentals inputs)
          Quad.twiceQuarter))
      selectedCayley)

-- The original double-angle and Pythagorean laws come from ONE
-- prior K05 product, not two additional trigonometric assumptions.
sourceMachinSinDoubleIsOneFromCayley :
  (inputs : Round11.Round11BishopCutset) →
  (product : Product.Round11ImaginaryExpMultiplicative inputs) →
  OriginalMachinCayleyHalfPhase inputs →
  R._≃_
    (Quad.sinDoublePolynomial
      (Quad.quarterCos inputs)
      (Quad.quarterSin inputs))
    R.1ℝ
sourceMachinSinDoubleIsOneFromCayley inputs product halfPhase =
  RP.≃-trans
    (RP.≃-symm
      (Quad.sineDouble
        (Product.round11DoubleAngleFromImaginaryProduct inputs product)
        Quarter.machinQuarterAngle))
    (sourceMachinHalfSineIsOneFromCayley inputs halfPhase)

-- No analytic hypothesis appears in this polynomial normalisation.
differenceSquareAsUnitMinusSineDouble :
  (c s : R.ℝ) →
  R._≃_
    (R._*_ (R._-_ c s) (R._-_ c s))
    (R._-_
      (R._+_ (R._*_ c c) (R._*_ s s))
      (Quad.sinDoublePolynomial c s))
differenceSquareAsUnitMinusSineDouble c s =
  let open RP.ℝ-Solver in
  solve 2
    (λ c s →
      (c ⊖ s) ⊗ (c ⊖ s)
      ⊜ ((c ⊗ c) ⊕ (s ⊗ s))
          ⊖ ((Κ (+ 2 / 1) ⊗ c) ⊗ s))
    RP.≃-refl c s

sourceMachinQuarterDifferenceSquareZero :
  (inputs : Round11.Round11BishopCutset) →
  (product : Product.Round11ImaginaryExpMultiplicative inputs) →
  OriginalMachinCayleyHalfPhase inputs →
  let
    c = Quad.quarterCos inputs
    s = Quad.quarterSin inputs
  in
  R._≃_
    (R._*_ (R._-_ c s) (R._-_ c s))
    R.0ℝ
sourceMachinQuarterDifferenceSquareZero inputs product halfPhase =
  let
    c = Quad.quarterCos inputs
    s = Quad.quarterSin inputs

    pythagorean =
      Product.round11PythagoreanFromImaginaryProduct
        inputs product Quarter.machinQuarterAngle
    sineDoubleOne =
      sourceMachinSinDoubleIsOneFromCayley inputs product halfPhase
    oneMinusOneIsZero :
      R._≃_ (R._-_ R.1ℝ R.1ℝ) R.0ℝ
    oneMinusOneIsZero =
      let open RP.ℝ-Solver in
      solve 0
        (Κ 1ℚᵘ ⊖ Κ 1ℚᵘ ⊜ Κ 0ℚᵘ)
        RP.≃-refl
  in
  RP.≃-trans
    (differenceSquareAsUnitMinusSineDouble c s)
    (RP.≃-trans
      (RP.+-cong pythagorean (RP.-‿cong sineDoubleOne))
      oneMinusOneIsZero)

sourceMachinQuarterEqualityFromCayley :
  (inputs : Round11.Round11BishopCutset) →
  (product : Product.Round11ImaginaryExpMultiplicative inputs) →
  OriginalMachinCayleyHalfPhase inputs →
  R._≃_ (Quad.quarterCos inputs) (Quad.quarterSin inputs)
sourceMachinQuarterEqualityFromCayley inputs product halfPhase =
  let
    c = Quad.quarterCos inputs
    s = Quad.quarterSin inputs
    diffZero =
      SquareZero.squareZeroReflectsSetoidZero
        (R._-_ c s)
        (sourceMachinQuarterDifferenceSquareZero
          inputs product halfPhase)
  in
  RP.≃-trans
    (let open RP.ℝ-Solver in
     solve 2
       (λ c s → c ⊜ (c ⊖ s) ⊕ s)
       RP.≃-refl c s)
    (RP.≃-trans
      (RP.+-cong diffZero RP.≃-refl)
      (RP.+-identityˡ s))

-- The full original source-native positive sine/first-zero compiler
-- now takes exactly one source-specific Cayley half-phase equation,
-- in addition to the common original K05 imaginary product.
sourceMachinFirstPositiveZeroFromCayley :
  (inputs : Round11.Round11BishopCutset) →
  (product : Product.Round11ImaginaryExpMultiplicative inputs) →
  OriginalMachinCayleyHalfPhase inputs →
  First.SourceMachinFirstPositiveSineZero inputs
sourceMachinFirstPositiveZeroFromCayley inputs product halfPhase =
  Global.round11MachinPiIsFirstPositiveSineZero
    inputs product
    (sourceMachinQuarterEqualityFromCayley inputs product halfPhase)
