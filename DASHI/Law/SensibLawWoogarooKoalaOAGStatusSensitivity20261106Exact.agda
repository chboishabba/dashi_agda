module DASHI.Law.SensibLawWoogarooKoalaOAGStatusSensitivity20261106Exact where

-- EPBC 2019/8575: exact rational reconstruction of the 14 printed
-- koala OAG area/quality gain rows, conditional on *reported* inputs.
--
-- Original numbers: Cherish/Saunders Havill Springfield PD v5 (30 Jan
-- 2026), Part A.i Tables A62, A69, A76; Esk BAAM A14, Avonvale One
-- Environment A15, MWW Saunders Havill A16. Original 2012 Department
-- "How to use the offsets assessment guide", section 2 A,C,G,H.
--
-- The 2026 PD expressly feeds the OAG "Vulnerable" koala (p=0.2%),
-- consistent with its 2019 referral status. The QLD/NSW/ACT koala was
-- relisted Endangered on 12 Feb 2022 (Commonwealth official listing).
-- Endangered OAG default p=1.2%. Whether old referral status is legally
-- the correct OAG input for 16 Oct 2026 approval is NOT decided here.
--
-- In this source model zero risk-of-loss differences are stipulated
-- as explicitly reported by the proponent. Only quality improvement
-- credit is counted. Competing physical/legal evidence is unadmitted.
-- This proof is an exact arithmetic sensitivity, not verified ecology,
-- exact accepted 15 Oct 2026 OAMP revision, official worksheet edit,
-- evidence of misconduct, appeal, enforcement or Court judgment.
--
-- Reuses original #1276 adversarial and offset owners. QUT/QCC and
-- consultants retain their separate research and submission authorship.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Law.SensibLawWoogarooOffsetCreditRobustnessCut20261106Exact as Credit

-- All areas in tenths of ha; future-minus-without offset quality in
-- integer OAG score points; confidence in percent. For each 14 rows:
-- score contribution (%) = areaTenths * deltaQ * confidence
--   / 8960 * (survivalPermille / 1000)^20.
-- Quantum impact 89.6 adjusted hectares is 896 tenths.
-- No round-until-end: source tables report 2-decimal rounded AU credits.

record QualityRow : Set where
  constructor quality-row
  field
    areaTenths : Nat
    gainQualityPoints : Nat
    futureConfidencePercent : Nat
open QualityRow public

weightedInput : QualityRow → Nat
weightedInput row =
  areaTenths row * gainQualityPoints row * futureConfidencePercent row

inputSum : List QualityRow → Nat
inputSum [] = 0
inputSum (row ∷ rows) = weightedInput row + inputSum rows

eskRows : List QualityRow
eskRows =
  quality-row 1501 1 75 ∷
  quality-row 448 2 75 ∷
  quality-row 759 1 85 ∷
  quality-row 94 1 85 ∷ []

avonvaleRows : List QualityRow
avonvaleRows =
  quality-row 493 3 75 ∷
  quality-row 152 4 75 ∷
  quality-row 20 1 85 ∷
  quality-row 868 2 75 ∷
  quality-row 110 0 85 ∷
  quality-row 37 1 85 ∷ []

mountWalkerRows : List QualityRow
mountWalkerRows =
  quality-row 508 4 75 ∷
  quality-row 1047 4 75 ∷
  quality-row 620 0 85 ∷
  quality-row 81 0 85 ∷ []

allRows : List QualityRow
allRows =
  quality-row 1501 1 75 ∷
  quality-row 448 2 75 ∷
  quality-row 759 1 85 ∷
  quality-row 94 1 85 ∷
  quality-row 493 3 75 ∷
  quality-row 152 4 75 ∷
  quality-row 20 1 85 ∷
  quality-row 868 2 75 ∷
  quality-row 110 0 85 ∷
  quality-row 37 1 85 ∷
  quality-row 508 4 75 ∷
  quality-row 1047 4 75 ∷
  quality-row 620 0 85 ∷
  quality-row 81 0 85 ∷ []

sourceWeightSum : inputSum allRows ≡ 1010350
sourceWeightSum = refl

separateSitesAddToSameWeight :
  inputSum eskRows + inputSum avonvaleRows + inputSum mountWalkerRows
    ≡ inputSum allRows
separateSitesAddToSameWeight = refl

-- Reconstruct OAG discounted quality credits using annual compounding.
-- The original 2012 OAG uses (1+p)^(-20), not (1-p)^20.
-- All published row values are reproduced to original display precision.
powNat : Nat → Nat → Nat
powNat base zero = 1
powNat base (suc n) = base * powNat base n

oagNumerator : Nat
oagNumerator = inputSum allRows * powNat 1000 20

vulnerableDenominator : Nat
vulnerableDenominator = 8960 * powNat 1002 20

endangeredDenominator : Nat
endangeredDenominator = 8960 * powNat 1012 20

-- Exact percentage formula:
-- numerator / denominator, with reported p=0.2% or hypothetical p=1.2%.
-- Approx 108.3451326195926% vs 88.8287572224147%.
-- No difference of rational numbers is silently rounded.
vulnerableAbove100Exact :
  100 * vulnerableDenominator +
    77820798575317738974523471040150835744595301920859529259515904000
    ≡ oagNumerator
vulnerableAbove100Exact = refl

endangeredBelow90Exact :
  oagNumerator +
    13321869823871146708748754453675736687701422609971835407066726400
    ≡ 90 * endangeredDenominator
endangeredBelow90Exact = refl

-- One MWW AU2 quality-gain point removed, all else held unchanged.
mwwAU2OnePointSensitivityWeight : Nat
mwwAU2OnePointSensitivityWeight = 1047 * 75

mwwAU2ReductionInputWeight :
  931825 + mwwAU2OnePointSensitivityWeight ≡ inputSum allRows
mwwAU2ReductionInputWeight = refl

mwwAU2ScenarioNumerator : Nat
mwwAU2ScenarioNumerator = 931825 * powNat 1000 20

onePointMWWAU2Below100Exact :
  mwwAU2ScenarioNumerator +
    704201424682261025476528959849164255404698079140470740484096000
    ≡ 100 * vulnerableDenominator
onePointMWWAU2Below100Exact = refl

onePointMWWAU2StillAbove90Exact :
  90 * vulnerableDenominator +
    92548718717785965077071123936135752170135771728773576333564313600
    ≡ mwwAU2ScenarioNumerator
onePointMWWAU2StillAbove90Exact = refl

sourceCreditFromPrior : Nat
sourceCreditFromPrior = Credit.allReportedCredit Credit.koala
