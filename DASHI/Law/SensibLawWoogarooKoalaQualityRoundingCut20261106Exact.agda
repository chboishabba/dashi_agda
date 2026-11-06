module DASHI.Law.SensibLawWoogarooKoalaQualityRoundingCut20261106Exact where

-- EPBC 2019/8575. ORIGINAL source: Cherish/Saunders Havill PD v5
-- (30 January 2026) Mount Walker West OAMP Table 13 and Part A.i
-- Table A76, AU1/AU2 baseline+future habitat-quality values.
-- This contrasts the SOURCE REPORTED unrounded ecological forecasts
-- with the SOURCE REPORTED rounded integer OAG quality input values.
--
-- Original authors QUT/QCC/RSPCA and offset consultants retain their
-- attribution. No official accepted 15 Oct 2026 source workbook, legal
-- precision rule, unlawful decision, ecological failure or Court finding
-- is inferred merely from conditional fractional calculation.

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Law.SensibLawWoogarooKoalaOAGStatusSensitivity20261106Exact as Koala

-- Integer OAG input points AU1/AU2: (7-3) and (7-3).
-- Original reported source ecological score AU1: (6.86-3.40) = 3.46;
-- AU2: (6.71-3.44) = 3.27.
-- Scale point gains by 100 for exact integer arithmetic.
mwwAU1SourceGainHundredths : 686 ≡ 340 + 346
mwwAU1SourceGainHundredths = refl

mwwAU2SourceGainHundredths : 671 ≡ 344 + 327
mwwAU2SourceGainHundredths = refl

mwwAU1RoundedGainHundredths : Nat
mwwAU1RoundedGainHundredths = 400

mwwAU2RoundedGainHundredths : Nat
mwwAU2RoundedGainHundredths = 400

mwwAU1RoundedInflationHundredths :
  346 + 54 ≡ mwwAU1RoundedGainHundredths
mwwAU1RoundedInflationHundredths = refl

mwwAU2RoundedInflationHundredths :
  327 + 73 ≡ mwwAU2RoundedGainHundredths
mwwAU2RoundedInflationHundredths = refl

-- Coefficients include AU area (tenths of ha), future-quality confidence
-- (75%) and 2012 OAG output scale. Preserve original modeled risk of
-- loss 0%, extinction 0.2%, time horizon 20y, impact 89.6 adjusted ha.
twoAURoundingDifferenceCoefficientHundredths : Nat
twoAURoundingDifferenceCoefficientHundredths =
  508 * 54 * 75 + 1047 * 73 * 75

twoAURoundingDifferenceExact :
  twoAURoundingDifferenceCoefficientHundredths ≡ 7789725
twoAURoundingDifferenceExact = refl

fullSourceCoefficientHundredths :
  Koala.inputSum Koala.allRows * 100 ≡ 101035000
fullSourceCoefficientHundredths = refl

unroundedOnlyTwoMWWAUCoefficient :
  93245275 + twoAURoundingDifferenceCoefficientHundredths
    ≡ Koala.inputSum Koala.allRows * 100
unroundedOnlyTwoMWWAUCoefficient = refl

-- Percentage (conditional):
-- [93245275/(100*8960)] * (1000/1002)^20 ~= 99.9918017%.
-- Compare original 108.3451326%. A paper source/model input precision
-- gate is needed before deciding whether rounding is permitted.
-- All remaining Esk, Avonvale and MWW AU inputs HELD AS REPORTED.
-- This is not a rerun of the official accepted OAG XLSM.

data OriginalPrecisionReceipt : Set where
  originalAcceptedOAGXLSM : OriginalPrecisionReceipt
  originalRoundingRule : OriginalPrecisionReceipt
  originalUnroundedMHQATransects : OriginalPrecisionReceipt
  delegateVersionSpecificReview : OriginalPrecisionReceipt

-- No value of OriginalPrecisionReceipt is constructed from paper
-- numbers or hypothetical arithmetic alone.
