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

-- Compute the exact OAG-type extinction discount without floating point.
-- It is a finite integer exponent (20), not a field measurement.
powNat : Nat → Nat → Nat
powNat base zero = 1
powNat base (suc n) = base * powNat base n

oagDenominator : Nat
oagDenominator = 8960 * powNat 1000 20

reportedVulnerableNumerator : Nat
reportedVulnerableNumerator = inputSum allRows * powNat 998 20

conditionalEndangeredNumerator : Nat
conditionalEndangeredNumerator = inputSum allRows * powNat 988 20

-- The decimal percentage is NUMERATOR / DENOMINATOR.
-- Vulnerable --> 108.336465... percent; Endangered --> 88.573280...
-- These comparisons prove strict bounds by exact nonnegative Nat gap,
-- not approximate numerical floating point.
vulnerableAbove100Exact :
  100 * oagDenominator +
    74694729431565397060899339608368338351827166358385744947812761600
    ≡ reportedVulnerableNumerator
vulnerableAbove100Exact = refl

endangeredBelow90Exact :
  conditionalEndangeredNumerator +
    12783410568185683280961630916019256474889973561150887111845478400
    ≡ 90 * oagDenominator
endangeredBelow90Exact = refl

-- If only Mount Walker West AU2's future quality changes 7 -> 6,
-- one quality-gain point is removed. Everything else is held fixed.
mwwAU2OnePointSensitivityWeight : Nat
mwwAU2OnePointSensitivityWeight = 1047 * 75

mwwAU2ReductionInputWeight :
  931825 + mwwAU2OnePointSensitivityWeight ≡ inputSum allRows
mwwAU2ReductionInputWeight = refl

mwwAU2ScenarioNumerator : Nat
mwwAU2ScenarioNumerator = 931825 * powNat 998 20

-- Absolute gap under 100 is source-derived and finite; no legal test.
-- Numerical approximate target 99.91649113%, before source AU rounding.

sourceCreditFromPrior : Nat
sourceCreditFromPrior = Credit.allReportedCredit Credit.koala
