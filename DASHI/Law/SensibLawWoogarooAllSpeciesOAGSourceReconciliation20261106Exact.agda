module DASHI.Law.SensibLawWoogarooAllSpeciesOAGSourceReconciliation20261106Exact where

-- EPBC 2019/8575. Original PD v5 30 Jan 2026 Part A.i tables:
-- A59, A63-65, A70-72, A77-79; BAAM Esk A14; One Environment
-- Avonvale A15; Saunders Havill Mount Walker West A16.
-- Source-internal arithmetic contradictions are not proof of intention,
-- fraud, future performance, actual Court/agency reliance or breach.
-- All original QUT/QCC/consultant and prior Agda/SLR attribution retained.
-- The actual approved 15 Oct 2026 offset worksheet remains a version
-- identity gate, not an object silently reconstructed from old PD.

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawWoogarooKoalaOAGStatusSensitivity20261106Exact as Koala
import DASHI.Law.SensibLawWoogarooOffsetCreditRobustnessCut20261106Exact as Credit

------------------------------------------------------------------------
-- Three site-wise source checks with internally contradictory printed
-- totals and genuine non-identical AU identifiers.
------------------------------------------------------------------------

-- MWW Table 19: Regent Honeyeater future-with-offset feature values,
-- 0 + 16720 + 1667 + 60 = 18447. Printed total is "45833", which is
-- the adjacent Table 17 Swift Parrot future feature total.
mwwRegentRowSum : 0 + 16720 + 1667 + 60 ≡ 18447
mwwRegentRowSum = refl

mwwRegentPrintedTotal : Nat
mwwRegentPrintedTotal = 45833

mwwRegentPrintedTotalNotRowSum :
  18447 ≡ mwwRegentPrintedTotal → ⊥
mwwRegentPrintedTotalNotRowSum ()

mwwSwiftFutureWithRowSum :
  16256 + 26752 + 2708 + 117 ≡ 45833
mwwSwiftFutureWithRowSum = refl

-- MWW Table 17 literal 'future without' column totals 0+0+30+109
-- = 139, but the printed column total is 227, matching START
-- 0+0+207+20. Published individual % credits cannot be reproduced
-- from those literal future-without rows using the reference OAG
-- feature-gain calculation. No source value may be silently replaced.
mwwSwiftLiteralWithoutRowSum : 0 + 0 + 30 + 109 ≡ 139
mwwSwiftLiteralWithoutRowSum = refl

mwwSwiftStartRowSum : 0 + 0 + 207 + 20 ≡ 227
mwwSwiftStartRowSum = refl

mwwSwiftFutureWithoutReportedTotalCannotBeLiteralSum :
  139 ≡ 227 → ⊥
mwwSwiftFutureWithoutReportedTotalCannotBeLiteralSum ()

-- Esk Table A64/A65 feature-area entries (in hundredths of hectares).
-- The second AU's 47.72 ha differs from the 44.8 ha used for other
-- Esk OAG rows. Literal four-row sum = 283.03, whereas printed TOTAL
-- = 280.03, and BAAM Table 7.3 area total = 280.2.
eskBirdLiteralAreaHundredths :
  15001 + 4772 + 7590 + 940 ≡ 28303
eskBirdLiteralAreaHundredths = refl

eskBirdPrintedAreaHundredths : Nat
eskBirdPrintedAreaHundredths = 28003

eskBirdLiteralAreaNotPrintedTotal :
  28303 ≡ eskBirdPrintedAreaHundredths → ⊥
eskBirdLiteralAreaNotPrintedTotal ()

-- A59 gives Esk Regent contribution 54.95; BAAM A14 7.3 gives
-- 54.96. Values in basis points: 5495 != 5496.
eskRegentMainPercentHundredths : Nat
eskRegentMainPercentHundredths = 5495
eskRegentBAAMPercentHundredths : Nat
eskRegentBAAMPercentHundredths = 5496
eskRegentReportedValuesDiffer :
  eskRegentMainPercentHundredths ≡
    eskRegentBAAMPercentHundredths → ⊥
eskRegentReportedValuesDiffer ()

------------------------------------------------------------------------
-- GHFF original 2012-OAG input-check: inverse annual discount p=0.2%
-- and 20 years. At identical site area and confidence, a 1-point
-- change in habitat quality has a strictly positive numerator effect.
-- We cannot force the rows to match without choosing which source
-- input to replace. These are model discrepancy *witnesses*, not claims
-- about the final approved workbook.
------------------------------------------------------------------------

-- Esk GHFF Table A63 AU2: area 44.8ha, printed baseline4 future8,
-- confidence 75%. Reported 10.81% is instead the 3-point gain
-- corresponding to baseline5 at the same area/time/confidence.
eskGHFFAU2PrintedQualityGain : 8 ≡ 4 + 4
eskGHFFAU2PrintedQualityGain = refl

eskGHFFAU2OutputImpliedGain :
  8 ≡ 5 + 3
eskGHFFAU2OutputImpliedGain = refl

eskGHFFAU2GainInputsDiffer :
  4 ≡ 3 → ⊥
eskGHFFAU2GainInputsDiffer ()

-- Avonvale GHFF Table A70 AU2: 15.2ha, baseline3 future7,
-- published 6.11% matches 5-point gain from baseline2, not
-- printed 4-point gain. Actual cause/source cell must be acquired.
avonGHFFAU2PrintedGain : 7 ≡ 3 + 4
avonGHFFAU2PrintedGain = refl

avonGHFFAU2OutputImpliedGain : 7 ≡ 2 + 5
avonGHFFAU2OutputImpliedGain = refl

avonGHFFAU2GainInputsDiffer :
  4 ≡ 5 → ⊥
avonGHFFAU2GainInputsDiffer ()

-- Earlier theorem checks the all-source 14-row koala alternative.
reusedKoalaInputCoefficient :
  Koala.inputSum Koala.allRows ≡ 1010350
reusedKoalaInputCoefficient = Koala.sourceWeightSum

reusedReportedKoalaCredit : Credit.allReportedCredit Credit.koala ≡ 10835
reusedReportedKoalaCredit = Credit.koalaTotal
