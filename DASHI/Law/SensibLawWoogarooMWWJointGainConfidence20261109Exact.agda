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
fiftyAbove90Exact :
  90 * jointDenominator +
    15573718717785965077071123936135752170135771728773576333564313600
    ≡ jointNumerator 4 50
fiftyAbove90Exact = refl

fiftyBelow100Exact :
  jointNumerator 4 50 +
    77679201424682261025476528959849164255404698079140470740484096000
    ≡ 100 * jointDenominator
fiftyBelow100Exact = refl

sixtyBelow100Exact :
  jointNumerator 4 60 +
    15479201424682261025476528959849164255404698079140470740484096000
    ≡ 100 * jointDenominator
sixtyBelow100Exact = refl

sixtyFiveAbove100Exact :
  100 * jointDenominator +
    15620798575317738974523471040150835744595301920859529259515904000
    ≡ jointNumerator 4 65
sixtyFiveAbove100Exact = refl

-- Joint feasible region with fixed other-site inputs is bounded by
-- product g*c. For full modeled coverage:
--   543850 + 1555*g*c >= 100*denominator / 1000^20.
-- For 90% direct, replace 100 by 90. Do not assert this is the
-- physically warranted probability, lawfulness, or measured habitat.
-- Rational thresholds are reconstructed in the companion verifier.

existingCommonGainReference :
  Existing.mwwBothQualityPointCoefficient ≡ 116625
existingCommonGainReference = Existing.perPointExactly
