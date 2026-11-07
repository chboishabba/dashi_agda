{-# OPTIONS --safe #-}
module DASHI.Geometry.GielisNineModeFourierExact where

------------------------------------------------------------------------
-- Selected m=9 FOUR-SAMPLE exact Fourier: native rational coordinates.
--
-- On Nyquist.Phase36 at j=0,1,2,3 we have four distinct quarter
-- phases for exp(2*pi*i*9*j/36). Their real character basis is:
--   1     [ 1, 1, 1, 1]
--   cos9  [ 1, 0,-1, 0]
--   sin9  [ 0, 1, 0,-1]
--   cos18 [ 1,-1, 1,-1].
--
-- The Fourier map and inverse are exact rational maps, not a
-- floating FFT. This is a *selected 4-dimensional subspace* of
-- the full 36-character cyclotomic theory, not a fake full C36 DFT.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; ½; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as Ring

import DASHI.Geometry.GielisBase369NyquistPhase36Exact as Nyquist

record FourSamples : Set where
  constructor four
  field
    value0 value1 value2 value3 : ℚ

open FourSamples public

record FourCoefficients : Set where
  constructor coeffs
  field
    dc cosine9 sine9 cosine18 : ℚ

open FourCoefficients public

fourQuarter : ℚ → ℚ
fourQuarter value = ½ * (½ * value)

fourHalf : ℚ → ℚ
fourHalf value = ½ * value

-- f_j=a+b cos(πj/2)+c sin(πj/2)+d(-1)^j.
fourierFour : FourSamples → FourCoefficients
fourierFour (four a b c d) =
  coeffs
    (fourQuarter (a + b + c + d))
    (fourHalf (a - c))
    (fourHalf (b - d))
    (fourQuarter ((a - b) + (c - d)))

inverseFourierFour : FourCoefficients → FourSamples
inverseFourierFour (coeffs a b c d) =
  four
    ((a + b) + d)
    ((a + c) - d)
    ((a - b) + d)
    ((a - c) - d)

fourierFourRoundTrip : (s : FourSamples) →
  inverseFourierFour (fourierFour s) ≡ s
fourierFourRoundTrip (four a b c d)
  rewrite Ring.solve-∀ a b c d
        | Ring.solve-∀ a b c d
        | Ring.solve-∀ a b c d
        | Ring.solve-∀ a b c d = refl

fourierFourCoefficientRoundTrip : (c : FourCoefficients) →
  fourierFour (inverseFourierFour c) ≡ c
fourierFourCoefficientRoundTrip (coeffs a b c d)
  rewrite Ring.solve-∀ a b c d
        | Ring.solve-∀ a b c d
        | Ring.solve-∀ a b c d
        | Ring.solve-∀ a b c d = refl

-- The actual fine-sampling surface is Nyquist.Phase36, not a
-- second four-phase cyclic carrier. We select four existing points
-- that distinguish the 9th-mode sine from its coarse alias.
selectNineQuarterSamples : (Nyquist.Phase36 → ℚ) → FourSamples
selectNineQuarterSamples f =
  four (f Nyquist.p36-0)
       (f Nyquist.p36-1)
       (f Nyquist.p36-2)
       (f Nyquist.p36-3)

reconstructNineQuarterSamples :
  (f : Nyquist.Phase36 → ℚ) →
  inverseFourierFour
    (fourierFour (selectNineQuarterSamples f))
  ≡ selectNineQuarterSamples f
reconstructNineQuarterSamples f =
  fourierFourRoundTrip (selectNineQuarterSamples f)

-- The lower-frequency 18-grid Nyquist alias is already proved in
-- GielisBase369NyquistPhase36Exact. The above four-point map
-- resolves all four independent 9-mode quarter-phase coefficients
-- once the relevant fine samples have been retained.
