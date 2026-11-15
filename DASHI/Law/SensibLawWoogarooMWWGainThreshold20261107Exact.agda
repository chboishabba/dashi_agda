module DASHI.Law.SensibLawWoogarooMWWGainThreshold20261107Exact where

-- EPBC 2019/8575. Source-only exact finite threshold with Esk,
-- Avonvale and all noncredit-bearing MWW AU values held at 30 Jan 2026
-- proponent PD Tables A62/A69/A76.
--
-- NOT a clinical ecological result, statutory 90% determination,
-- official final Oct 2026 OAG worksheet, observed restoration or
-- conclusion that four-point improvements cannot be substantiated.
--
-- Confidence 75%, 20-year OAG inverse-compounding discount, vulnerable
-- 0.2% are held at original submitted source values. The two MWW
-- credit-bearing units together contribute 116625 coefficient units
-- per ONE common quality-gain point. The other source rows contribute
-- 543850. All source provenance is preserved in KoalaOAGStatusSensitivity.

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Law.SensibLawWoogarooKoalaOAGStatusSensitivity20261106Exact as Koala

otherSiteCoefficient : Nat
otherSiteCoefficient = Koala.inputSum Koala.eskRows +
                       Koala.inputSum Koala.avonvaleRows

otherSitesExact : otherSiteCoefficient ≡ 543850
otherSitesExact = refl

mwwBothQualityPointCoefficient : Nat
mwwBothQualityPointCoefficient = (508 + 1047) * 75

perPointExactly : mwwBothQualityPointCoefficient ≡ 116625
perPointExactly = refl

scenarioNumerator : Nat → Nat
scenarioNumerator gain =
  (otherSiteCoefficient + mwwBothQualityPointCoefficient * gain) *
  Koala.powNat 1000 20

denominator : Nat
denominator = Koala.vulnerableDenominator

-- Exact rational threshold: proposed percentage C(g) equals
-- scenarioNumerator(g)/denominator. With other inputs fixed:
-- g=2 => C(g)≈83.33251% (less than 90)
-- g=3 => C(g)≈95.83882% (at least 90 but less than 100)
-- g=4 => C(g)≈108.34513% (at least 100).
--
-- All claims are proved by canonical normalization of exact Nat
-- equalities, not by float and not by a guessed physical forecast.
twoPointBelow90Witness :
  scenarioNumerator 2 +
  62176281282214034922928876063864247829864228271226423666435686400
  ≡ 90 * denominator
twoPointBelow90Witness = refl

threePointAbove90Witness :
  90 * denominator +
  54448718717785965077071123936135752170135771728773576333564313600
  ≡ scenarioNumerator 3
threePointAbove90Witness = refl

threePointBelow100Witness :
  scenarioNumerator 3 +
  38804201424682261025476528959849164255404698079140470740484096000
  ≡ 100 * denominator
threePointBelow100Witness = refl

fourPointAbove100Witness :
  100 * denominator +
  77820798575317738974523471040150835744595301920859529259515904000
  ≡ scenarioNumerator 4
fourPointAbove100Witness = refl

-- For a COMMON equal improvement g, the exact 90% threshold is
-- ((90 * denominator / 1000^20) - 543850) / 116625;
-- for 100%, replace 90 by 100. The exact-rational Python reference
-- calculates these thresholds without rounding them to 3/4 points.
-- For unequal AU gains, replace 116625*g by
-- 508*75*g_AU1 + 1047*75*g_AU2.
--
-- No evidence is assigned to a claimed exceptional >1 OAG quality
-- gain merely by proving these hypothetical arithmetic inequalities.
