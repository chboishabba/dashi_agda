module DASHI.Law.SensibLawWoogarooOffsetCreditRobustnessCut20261106Exact where

-- Original evidence: Cherish/Saunders Havill Springfield Preliminary
-- Documentation v5 (30 January 2026), Part A.i Table A59. These are
-- PROPONENT-REPORTED OAG summaries, NOT actual measured future benefits.
-- Original QUT/QCC authorship and existing dashi_agda PR #1276 adversarial
-- owner are preserved. See 6 November 2026 source ledger for PDF identity.
--
-- Exact arithmetic in "basis points" of *percentage compensation*:
-- 10000 = 100.00 percent of impact, NOT probability or habitat score.
-- This is a post-OAG reported-credit sensitivity layer, not the actual
-- 2012 OAG NPV formula. Conditional retention shocks are illustrative.
-- Independent field/approved-calculator validation and legal conclusions
-- remain strictly outside this algebraic finite model.

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawWoogarooProponentEvidenceAdversarialAudit20261106Exact as Audit
import DASHI.Law.SensibLawWoogarooAdversarialLogicalTests20261028Exact as Prior
import DASHI.Law.SensibLawWoogarooEPBC8575PleadableGroundsPrecedentCut20261028Exact as Grounds

data Matter : Set where
  koala flyingFox swiftParrot regentHoneyeater : Matter

data Site : Set where
  esk avonvale mountWalkerWest : Site

reportedCredit : Matter → Site → Nat
reportedCredit koala esk = 2706
reportedCredit koala avonvale = 3127
reportedCredit koala mountWalkerWest = 5002
reportedCredit flyingFox esk = 6344
reportedCredit flyingFox avonvale = 6059
reportedCredit flyingFox mountWalkerWest = 6689
reportedCredit swiftParrot esk = 5458
reportedCredit swiftParrot avonvale = 5349
reportedCredit swiftParrot mountWalkerWest = 9192
reportedCredit regentHoneyeater esk = 5495
reportedCredit regentHoneyeater avonvale = 1207
reportedCredit regentHoneyeater mountWalkerWest = 3740

allReportedCredit : Matter → Nat
allReportedCredit m =
  reportedCredit m esk + reportedCredit m avonvale +
  reportedCredit m mountWalkerWest

koalaTotal : allReportedCredit koala ≡ 10835
koalaTotal = refl

flyingFoxTotal : allReportedCredit flyingFox ≡ 19092
flyingFoxTotal = refl

swiftParrotTotal : allReportedCredit swiftParrot ≡ 19999
swiftParrotTotal = refl

regentHoneyeaterTotal : allReportedCredit regentHoneyeater ≡ 10442
regentHoneyeaterTotal = refl

-- Baseline source claims all exceed 10000; positive MARGINS below are
-- arithmetic from the printed table, NOT a confidence bound.
koalaMargin : 10000 + 835 ≡ allReportedCredit koala
koalaMargin = refl

flyingFoxMargin : 10000 + 9092 ≡ allReportedCredit flyingFox
flyingFoxMargin = refl

swiftParrotMargin : 10000 + 9999 ≡ allReportedCredit swiftParrot
swiftParrotMargin = refl

regentHoneyeaterMargin : 10000 + 442 ≡ allReportedCredit regentHoneyeater
regentHoneyeaterMargin = refl

-- Exact 100%-requirement cut, HOLDING other two sites at source claims.
-- These retained MWW percentages are required by arithmetic, not by
-- independent ecological evidence or a statutory 100% proof obligation.
koalaOtherSites : reportedCredit koala esk +
  reportedCredit koala avonvale ≡ 5833
koalaOtherSites = refl

koalaMWW100Boundary :
  reportedCredit koala esk + reportedCredit koala avonvale + 4167
  ≡ 10000
koalaMWW100Boundary = refl

koalaMWW100OneBelow :
  reportedCredit koala esk + reportedCredit koala avonvale + 4166
  ≡ 9999
koalaMWW100OneBelow = refl

koalaMWW90Boundary :
  reportedCredit koala esk + reportedCredit koala avonvale + 3167
  ≡ 9000
koalaMWW90Boundary = refl

regentOtherSites : reportedCredit regentHoneyeater esk +
  reportedCredit regentHoneyeater avonvale ≡ 6702
regentOtherSites = refl

regentMWW100Boundary :
  reportedCredit regentHoneyeater esk +
  reportedCredit regentHoneyeater avonvale + 3298 ≡ 10000
regentMWW100Boundary = refl

regentMWW100OneBelow :
  reportedCredit regentHoneyeater esk +
  reportedCredit regentHoneyeater avonvale + 3297 ≡ 9999
regentMWW100OneBelow = refl

regentMWW90Boundary :
  reportedCredit regentHoneyeater esk +
  reportedCredit regentHoneyeater avonvale + 2298 ≡ 9000
regentMWW90Boundary = refl

-- A conservative, scale-free *post-OAG retained-credit* shock only.
-- Define 10, 12 and 20 percent reductions in the reported MWW
-- contributions while holding Esk and Avonvale unchanged. Fractions
-- are kept by multiplying all credit totals by 100 (no rounding).
retainedCreditHundredths : Matter → Nat → Nat
retainedCreditHundredths m retentionPercent =
  100 * (reportedCredit m esk + reportedCredit m avonvale)
  + retentionPercent * reportedCredit m mountWalkerWest

koalaMWW90PercentRetained :
  retainedCreditHundredths koala 90 ≡ 1033480
koalaMWW90PercentRetained = refl

regentMWW90PercentRetained :
  retainedCreditHundredths regentHoneyeater 90 ≡ 1006800
regentMWW90PercentRetained = refl

regentMWW88PercentRetained :
  retainedCreditHundredths regentHoneyeater 88 ≡ 999320
regentMWW88PercentRetained = refl

koalaMWW80PercentRetained :
  retainedCreditHundredths koala 80 ≡ 983460
koalaMWW80PercentRetained = refl

-- Both parties' counterfactuals must still be tested: this finite
-- arithmetic neither shows incorrect OAG inputs nor real-world gains.
oldAudit : Audit.ProponentEvidenceReview
oldAudit = Audit.review Audit.futureHabitatValue

priorLegalCaseCountermodel :
  Prior.ShortcutCountermodel
    Grounds.actionBaselineError
priorLegalCaseCountermodel = Audit.priorLegalHabitatCountermodel

data SourceReportedCompensationIsRealisedOutcome : Set where
sourceCreditNotReality :
  SourceReportedCompensationIsRealisedOutcome → ⊥
sourceCreditNotReality ()

data SensitivityShockIsOfficialOAGRecalculation : Set where
noOfficialRecalculationFromShock :
  SensitivityShockIsOfficialOAGRecalculation → ⊥
noOfficialRecalculationFromShock ()
