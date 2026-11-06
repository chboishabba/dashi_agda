{-# OPTIONS --safe #-}
module DASHI.Foundations.BishopMachinRationalGaussianPhaseExact where

------------------------------------------------------------------------
-- K05-PI: EXACT RATIONAL GAUSSIAN MACHIN PHASE, NOT TRIG SEMANTICS.
--
-- For the original arctangent arguments t=1/5 and t=1/239, the
-- rational Cayley phases (1+i*t)/(1-i*t) have coordinates
--    q_5   = 12/13    + i*(5/13)
--    q_239 = 28560/28561 + i*(239/28561).
--
-- The FOURTH power q_5^4 has coordinates
--    (-239/28561, 28560/28561)
-- and q_5^4 * conjugate(q_239) = i exactly.
--
-- This supplies the precise finite Gaussian arithmetic needed AFTER
-- proving the source-native Bishop analytic bridge
--   exp_C(2*i*atan_B(t)) ~= (1+i*t)/(1-i*t).
-- The latter is not inferred by this module. No new real carrier,
-- classical sine/cosine, pi, or analytic assumptions are introduced.
--
-- Machin (1706), Bishop/Bridges, Murray/Csimma; existing DASHI
-- BishopMachinRationalTangentAlgebraExact owner.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_; _*_; _/_)
open import Agda.Builtin.Equality using (_≡_)
import Data.Rational.Tactic.RingSolver as ℚRing

phaseFiveReal phaseFiveImag phase239Real phase239Imag : ℚ
phaseFiveReal = + 12 / 13
phaseFiveImag = + 5 / 13
phase239Real = + 28560 / 28561
phase239Imag = + 239 / 28561

squareReal : ℚ → ℚ → ℚ
squareReal a b = a * a - b * b

squareImag : ℚ → ℚ → ℚ
squareImag a b = (a + a) * b

phaseFiveSquareReal phaseFiveSquareImag : ℚ
phaseFiveSquareReal = squareReal phaseFiveReal phaseFiveImag
phaseFiveSquareImag = squareImag phaseFiveReal phaseFiveImag

phaseFiveFourthReal phaseFiveFourthImag : ℚ
phaseFiveFourthReal =
  squareReal phaseFiveSquareReal phaseFiveSquareImag
phaseFiveFourthImag =
  squareImag phaseFiveSquareReal phaseFiveSquareImag

phaseFiveFourthRealExact :
  phaseFiveFourthReal ≡ (+ 0 / 1) - (+ 239 / 28561)
phaseFiveFourthRealExact = ℚRing.solve-∀

phaseFiveFourthImagExact :
  phaseFiveFourthImag ≡ + 28560 / 28561
phaseFiveFourthImagExact = ℚRing.solve-∀

-- q_5^4 * conjugate(q_239) = i.
-- Real component: a*c + b*d, because the conjugate has -d.
machinQuarterGaussianReal : ℚ
machinQuarterGaussianReal =
  phaseFiveFourthReal * phase239Real
  + phaseFiveFourthImag * phase239Imag

machinQuarterGaussianImag : ℚ
machinQuarterGaussianImag =
  phaseFiveFourthImag * phase239Real
  - phaseFiveFourthReal * phase239Imag

machinQuarterGaussianRealZero :
  machinQuarterGaussianReal ≡ + 0 / 1
machinQuarterGaussianRealZero = ℚRing.solve-∀

machinQuarterGaussianImagOne :
  machinQuarterGaussianImag ≡ + 1 / 1
machinQuarterGaussianImagOne = ℚRing.solve-∀

-- The two unit-modulus identities are independent rational checks
-- needed when converting the rational conjugate into an inverse.
phaseFiveUnitModulus :
  phaseFiveReal * phaseFiveReal + phaseFiveImag * phaseFiveImag
  ≡ + 1 / 1
phaseFiveUnitModulus = ℚRing.solve-∀

phase239UnitModulus :
  phase239Real * phase239Real + phase239Imag * phase239Imag
  ≡ + 1 / 1
phase239UnitModulus = ℚRing.solve-∀
