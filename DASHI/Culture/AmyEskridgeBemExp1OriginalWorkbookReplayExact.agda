module DASHI.Culture.AmyEskridgeBemExp1OriginalWorkbookReplayExact where

-- Original user-supplied EXP1.xlsx, inspected 2026-11-18 with artifact_tool.
-- SHA-256 feadd752a26f997327f12921eb916d9154b9907e27205aca64b9a22a0ea2df45
-- Primary source: https://replicationindex.com/wp-content/uploads/2018/01/exp1.xlsx
-- 100 rows of original participant/session summaries; the original 2011
-- paper's Experiment 1 is correctly reproduced by a one-sided ONE-SAMPLE
-- t test on 100 participants' percentages (mean 53.1388889%, sample
-- SD 12.4892709%, t(99)=2.5132683, one-sided p=0.006787827).
-- Controls 49.8333333% (t=-0.14575; one-sided p=.55779).
-- High seeking is source-defined STRICTLY >2.5 (n=42), giving
-- 57.6058201% (t(41)=4.5701353, one-sided p=2.208586e-5).
-- Low seeking <=2.5 (n=58), 49.9042146% (t=-0.0573).
-- Correlation r=.1821491, one-sided p=.0348546.
-- Predeclared cutoff status cannot be established from summary XLSX.
-- First 40 participant sessions: 12 erotic trials each (261 hits/480),
-- last 60: 18 erotic trials each (565 hits/1080).
-- Thus source workbook reconstructs 826/1560, not the 828/1560
-- claimed in Walleczek et al 2025 (doi 10.1371/journal.pone.0335330).
-- Note 2011 original reports rounded 53.1% and t(99)=2.51, p=.01
-- at 1/100 precision; it is CONSISTENT with this dataset.
-- The 53.1388889% is the unweighted PARTICIPANT MEAN, whereas
-- 826/1560=52.9487179% is the TRIAL-POOLED rate. Do not equate them.
-- This module proves integer identity/boundary claims only; actual t
-- distribution p-values computed by independently replayable SciPy
-- and should never be represented as kernel-computed distribution CDFs.
-- No participant source records or personal details are committed here.

open import Agda.Builtin.Nat using (Nat; _+_; _*_; zero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Culture.AmyEskridgeBemOriginalProtocolCorrespondenceWeldExact as Hist
import DASHI.Culture.AmyEskridgeBemSteelmanRealisticIdentifiabilityExact as Steelman

record OriginalWorkbookReceipt : Set where
  constructor original-workbook-receipt
  field
    checksum : String
    sourceName : String
    sessions : Nat
    firstEpochSessions : Nat
    lastEpochSessions : Nat
    firstEpochEroticHits : Nat
    lastEpochEroticHits : Nat
    firstEpochTrialsPerSession : Nat
    lastEpochTrialsPerSession : Nat
    highStimulusSeekers : Nat
    lowStimulusSeekers : Nat
    independentlyReproducedPrimaryTest : String
    limitations : String
open OriginalWorkbookReceipt public

sourceExp1 : OriginalWorkbookReceipt
sourceExp1 = original-workbook-receipt
  "feadd752a26f997327f12921eb916d9154b9907e27205aca64b9a22a0ea2df45"
  "uploaded exp1.xlsx — '#1 Precog Detection of Erotica'"
  100 40 60 261 565 12 18 42 58
  "100 participant-level erotic percentages vs 50%: t(99)=2.513268326486214, one-sided p=0.006787827163316628; matches Bem rounded t(99)=2.51, 53.1%"
  "Summary percentages, not RNG target location/trial records; no original 2011 analysis preregistration or experiment-wide selection data"

originalParticipantTotal :
  firstEpochSessions sourceExp1 + lastEpochSessions sourceExp1
    ≡ sessions sourceExp1
originalParticipantTotal = refl

sourceFirstEpochMatchesOriginalCorrespondence :
  firstEpochSessions sourceExp1 ≡ Hist.sampleCount Hist.bemExp1First40
sourceFirstEpochMatchesOriginalCorrespondence = refl

sourceLastEpochMatchesOriginalCorrespondence :
  lastEpochSessions sourceExp1 ≡ Hist.sampleCount Hist.bemExp1Later60
sourceLastEpochMatchesOriginalCorrespondence = refl

originalEroticTrials : Nat
originalEroticTrials =
  firstEpochSessions sourceExp1 * firstEpochTrialsPerSession sourceExp1
  + lastEpochSessions sourceExp1 * lastEpochTrialsPerSession sourceExp1

originalHitCount : Nat
originalHitCount =
  firstEpochEroticHits sourceExp1 + lastEpochEroticHits sourceExp1

trialCountFromSource : originalEroticTrials ≡ 1560
trialCountFromSource = refl

hitCountFromSource : originalHitCount ≡ 826
hitCountFromSource = refl

highLowParticipants : highStimulusSeekers sourceExp1 +
  lowStimulusSeekers sourceExp1 ≡ sessions sourceExp1
highLowParticipants = refl

-- Source-weighted rate is exactly 826/1560. The participant mean is
-- (261/12 + 565/18) / 100, i.e. 9565/180 percent.
unweightedParticipantMeanNumerator : Nat
unweightedParticipantMeanNumerator =
  (firstEpochEroticHits sourceExp1 * 3)
  + (lastEpochEroticHits sourceExp1 * 2)

unweightedMeanNumerator :
  unweightedParticipantMeanNumerator ≡ 1913
unweightedMeanNumerator = refl

-- 1913/36 is 53.1388889 percent, i.e. probability 1913/3600.
-- Compare it to 826/1560 as a PROBABILITY, not to its percent scale.
weightedPercentageIsNotParticipantMean :
  826 * 3600 ≡ 1913 * 1560 → ⊥
weightedPercentageIsNotParticipantMean ()

laterPublished828IsDifferentFromUploaded826 :
  originalHitCount ≡ 828 → ⊥
laterPublished828IsDifferentFromUploaded826 ()

sourceDateEpochAndPrimaryStatisticDistinct :
  Steelman.reportedTrialCount (Steelman.observed Steelman.strongestSteelman)
    ≡ originalEroticTrials
sourceDateEpochAndPrimaryStatisticDistinct = refl
