module DASHI.Cognition.CCDCOEP3PreAPIOpinionTemporalControlExact where

------------------------------------------------------------------------
-- ACTUAL PRE-API NATIONAL CLIMATE OPINION SURVEY MEASUREMENTS.
-- Jon A. Krosnick, Penny Visser and Allyson Holbrook,
-- "American Opinion on Global Warming: The Impact of the Fall 1997
-- Debate", Resources for the Future / Resources, 31 Oct 1998.
-- https://www.resources.org/archives/
-- american-opinion-on-global-warming-the-impact-of-the-fall-1997-debate/
-- DOI 10.1088/0963-6625/9/3/303 (published study, 2000).
--
-- 688 sampled US adults Sept 1-Oct 5 1997, 725 Dec 20 1997-Feb 13
-- 1998. BOTH complete before the April 3 1998 API plan.
-- These are source-reported rounded cross-sectional descriptive
-- measurements, not original respondent microdata or a randomized
-- estimate of effects of the API plan.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF

data SurveyWave : Set where
  before1997KyotoDebate : SurveyWave
  after1997DebateBeforeAPIDraft : SurveyWave

record PublishedWave : Set where
  constructor publishedWave
  field
    surveyDateRange : String
    sampleSize : Nat
    endedBeforeApril1998APIPlan : Bool

sourceWave : SurveyWave → PublishedWave
sourceWave before1997KyotoDebate =
  publishedWave "1997-09-01 through 1997-10-05" 688 true
sourceWave after1997DebateBeforeAPIDraft =
  publishedWave "1997-12-20 through 1998-02-13" 725 true

surveyN0 : PublishedWave.sampleSize
  (sourceWave before1997KyotoDebate) ≡ 688
surveyN0 = refl

surveyN1 : PublishedWave.sampleSize
  (sourceWave after1997DebateBeforeAPIDraft) ≡ 725
surveyN1 = refl

bothWavesPrecedeAPIDraft :
  (wave : SurveyWave) →
  PublishedWave.endedBeforeApril1998APIPlan (sourceWave wave) ≡ true
bothWavesPrecedeAPIDraft before1997KyotoDebate = refl
bothWavesPrecedeAPIDraft after1997DebateBeforeAPIDraft = refl

data MeasuredQuestion : Set where
  recalledNewsCoverage
  thoughtALotOrModerate
  highOpinionCertainty
  strongPartyGapHistoricalWarming
  strongPartyGapFutureWarming : MeasuredQuestion

-- Published source percentages, rounded, and party-gap
-- percentage points. No shared denominator claim for the subgroups.
reportedPercentage : MeasuredQuestion → SurveyWave → Nat
reportedPercentage recalledNewsCoverage before1997KyotoDebate = 48
reportedPercentage recalledNewsCoverage after1997DebateBeforeAPIDraft = 56
reportedPercentage thoughtALotOrModerate before1997KyotoDebate = 54
reportedPercentage thoughtALotOrModerate after1997DebateBeforeAPIDraft = 65
reportedPercentage highOpinionCertainty before1997KyotoDebate = 28
reportedPercentage highOpinionCertainty after1997DebateBeforeAPIDraft = 34
reportedPercentage strongPartyGapHistoricalWarming before1997KyotoDebate = 4
reportedPercentage strongPartyGapHistoricalWarming after1997DebateBeforeAPIDraft = 17
reportedPercentage strongPartyGapFutureWarming before1997KyotoDebate = 8
reportedPercentage strongPartyGapFutureWarming after1997DebateBeforeAPIDraft = 21

-- Arithmetic differences are descriptive percentage-point changes
-- across TWO reported samples; not unit-level treatment effects.
newsExposureDifference :
  reportedPercentage recalledNewsCoverage before1997KyotoDebate + 8
  ≡ reportedPercentage recalledNewsCoverage after1997DebateBeforeAPIDraft
newsExposureDifference = refl

thinkingDifference :
  reportedPercentage thoughtALotOrModerate before1997KyotoDebate + 11
  ≡ reportedPercentage thoughtALotOrModerate after1997DebateBeforeAPIDraft
thinkingDifference = refl

partyGapDifference :
  reportedPercentage strongPartyGapHistoricalWarming before1997KyotoDebate + 13
  ≡ reportedPercentage strongPartyGapHistoricalWarming
      after1997DebateBeforeAPIDraft
partyGapDifference = refl

-- Two hypothetical later campaign outcomes are compatible with the
-- exact same original 1997 survey observations. The earlier survey
-- is not an effect-of-later-action measurement.
data LaterWorld : Set where
  laterPlanHasNoEstablishedImpact : LaterWorld
  laterPlanHasIndependentEstablishedImpact : LaterWorld

data LaterImpact : Set where
  noVerifiedImpact : LaterImpact
  verifiedImpact : LaterImpact

observedEarlierWaves : LaterWorld → Nat
observedEarlierWaves _ = 688 + 725

laterImpact : LaterWorld → LaterImpact
laterImpact laterPlanHasNoEstablishedImpact = noVerifiedImpact
laterImpact laterPlanHasIndependentEstablishedImpact = verifiedImpact

earlierSurveyCannotIdentifyLaterCampaignEffect :
  NF.FactorsThrough observedEarlierWaves laterImpact → ⊥
earlierSurveyCannotIdentifyLaterCampaignEffect =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness
      laterPlanHasNoEstablishedImpact
      laterPlanHasIndependentEstablishedImpact
      refl (λ ()))

-- Distinguishing direct 1998 plan exposure and measured outcomes still
-- requires source-specific post-plan observations. Synthetic world
-- labels are NOT observed people, a past campaign effect, or any
-- claim about the legitimacy of dissent.
