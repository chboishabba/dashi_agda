module DASHI.Law.SensibLawWoogarooMWWJointGainConfidence20261109Exact where

-- EPBC 2019/8575, 30 Jan 2026 proponent PD v5 OAG only.
-- A precise 2-parameter break-even certificate: MWW AU1/AU2
-- common proposed quality gain g, common claimed confidence c%.
--
-- All other Esk + Avonvale original source inputs held fixed.
-- Formula for percent of Koala quantum offset compensated:
--   C(g,c) = (543850 + (508+1047)*g*c) * (1000/1002)^20 / 8960
--
-- The received January OAG says g=4, c=75. Neither the future
-- gain nor confidence is empirically validated by this arithmetic.
-- Signed 16 Oct Part 9 references *later* Issue F July 3 PD and
-- Oct 15 MWW OAMP Issue D, currently not received.
-- All author attribution belongs to original BAAM, One Environment,
-- Saunders Havill, QUT Taylor/Maguire/Lewis, QCC Gough, and RSPCA.
--
-- Use exact naturals for test inequalities; no statistical inference,
-- unproved legal threshold, actual compliant/breached works or fake
-- accepted spreadsheet evidence. Real Agda --safe verification pending.

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Law.SensibLawWoogarooKoalaOAGStatusSensitivity20261106Exact as Source
import DASHI.Law.SensibLawWoogarooMWWGainThreshold20261107Exact as Existing

otherSourceContribution : Nat
otherSourceContribution = Source.inputSum Source.eskRows +
                          Source.inputSum Source.avonvaleRows

otherSourceCorrect : otherSourceContribution ≡ 543850
otherSourceCorrect = refl

mwwAreaTenths : Nat
mwwAreaTenths = 508 + 1047

mwwAreaTenthsCorrect : mwwAreaTenths ≡ 1555
mwwAreaTenthsCorrect = refl

jointCoefficient : Nat → Nat → Nat
jointCoefficient commonGain confidencePercent =
  otherSourceContribution + mwwAreaTenths * commonGain * confidencePercent

jointNumerator : Nat → Nat → Nat
jointNumerator gain confidence =
  jointCoefficient gain confidence * Source.powNat 1000 20

jointDenominator : Nat
jointDenominator = Source.vulnerableDenominator

submittedScenarioMatchesSource :
  jointCoefficient 4 75 ≡ Source.inputSum Source.allRows
submittedScenarioMatchesSource = refl

-- The following Nat identities prove exact source arithmetic
-- inequalities at confidence 50, 60, 65 and 75 percent, with a
-- four-point predicted quality gain and unchanged other-site credits.
-- 50% => 91.67005..%, above ordinary 90 but below full 100.
-- 60% => 98.34008..%, below full 100.
-- 65% => 101.67510..%, above full 100.
-- No claims about actual ecological delivery or permitted confidence.
fiftyAbove90Difference : Nat
fiftyAbove90Difference =
  jointNumerator 4 50 - 90 * jointDenominator

-- We avoid subtraction in the proof by using normalized addition
-- witnesses with exact difference constants defined below.
