module DASHI.Cognition.CCDCOEP3G20ComplianceObservedExact where

------------------------------------------------------------------------
-- ORIGINAL EMPIRICAL CREDIT: G20 Research Group (University of Toronto)
-- and named IORI HSE/RANEPA research collaborators. This module
-- TRANSCRIBES published selected-commitment scoring summaries. These
-- scores are not authored by the G20 leaders and are not newly measured
-- by DASHI. In particular scoring a selected policy action is NOT
-- measuring changes in emissions, no causal industry influence and
-- not source corroboration of a full commitment universe.
--
-- 2014 Brisbane Final Compliance Report, issued 12 Nov 2015:
-- 17 selected of 205 summit commitments, actions 16 Nov 2014 -
-- 01 Oct 2015; authors Montpetit, Mladenova, Deprez, Tavone,
-- Gazaleh, Grott, Tsapralis, Sakharov, Shelepov, Rakhmangulov.
-- Climate +.10 (55%), clean energy +.90 (95%),
-- fossil-fuel subsidies -.45 (28% rounded).
--
-- 2015 Antalya Final Compliance Report, issued 3 Sep 2016,
-- revised 10 Dec 2016: 17 selected of 113; actions 16 Nov 2015
-- - 5 Sep 2016; authors Scott, Wang and G20 Research Group,
-- Rakhmangulov and RANEPA. Fossil subsidies -.35 (33% rounded).
--
-- Original reports retain complete authorship and interpretation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

data IndependentStudy : Set where
  brisbaneFinal2014 : IndependentStudy
  antalyaFinal2015 : IndependentStudy

data MeasuredCategory : Set where
  climateCommitment : MeasuredCategory
  cleanEnergyTechnology : MeasuredCategory
  fossilFuelSubsidyReform : MeasuredCategory

data SelectedScore : Set where
  brisbaneClimate : SelectedScore
  brisbaneCleanEnergy : SelectedScore
  brisbaneFossil : SelectedScore
  antalyaFossil : SelectedScore

sourceStudy : SelectedScore → IndependentStudy
sourceStudy brisbaneClimate = brisbaneFinal2014
sourceStudy brisbaneCleanEnergy = brisbaneFinal2014
sourceStudy brisbaneFossil = brisbaneFinal2014
sourceStudy antalyaFossil = antalyaFinal2015

category : SelectedScore → MeasuredCategory
category brisbaneClimate = climateCommitment
category brisbaneCleanEnergy = cleanEnergyTechnology
category brisbaneFossil = fossilFuelSubsidyReform
category antalyaFossil = fossilFuelSubsidyReform

-- Rounded percentages AS PUBLISHED; a printed -0.45 on the -1/+1
-- score scale yields a 27.5% nominal conversion rounded to 28%.
-- This is NOT the share of countries achieving the goal.
reportedPercent : SelectedScore → Nat
reportedPercent brisbaneClimate = 55
reportedPercent brisbaneCleanEnergy = 95
reportedPercent brisbaneFossil = 28
reportedPercent antalyaFossil = 33

data Population : Set where
  selectedSeventeenOfBrisbane205 : Population
  selectedSeventeenOfAntalya113 : Population

scoringPopulation : IndependentStudy → Population
scoringPopulation brisbaneFinal2014 = selectedSeventeenOfBrisbane205
scoringPopulation antalyaFinal2015 = selectedSeventeenOfAntalya113

record IndependentEvaluation : Set where
  constructor independentEvaluation
  field
    originatingReport : String
    originalReviewAuthors : String
    selectedCommitmentCount : Nat
    completeSummitCommitmentCount : Nat
    observationStart : String
    observationEnd : String
    sourceReviewerHashVerified : Bool
    originalAuthorsEndorseDASHI : Bool
    causalGCCOrExxonEffectMeasured : Bool
    emissionsPerformanceMeasured : Bool

study : IndependentStudy → IndependentEvaluation
study brisbaneFinal2014 =
  independentEvaluation
    "G20 Research Group Brisbane Final Compliance Report, 2015"
    "Montpetit, Mladenova, Deprez, Tavone, Gazaleh, Grott, Tsapralis; Sakharov, Shelepov, Rakhmangulov"
    17 205 "2014-11-16" "2015-10-01" false false false false
study antalyaFinal2015 =
  independentEvaluation
    "G20 Research Group Antalya Final Compliance Report, 2016"
    "Scott, Wang, G20 Research Group; Rakhmangulov, RANEPA"
    17 113 "2015-11-16" "2016-09-05" false false false false

brisbaneClimateReported :
  reportedPercent brisbaneClimate ≡ 55
brisbaneClimateReported = refl

brisbaneCleanEnergyReported :
  reportedPercent brisbaneCleanEnergy ≡ 95
brisbaneCleanEnergyReported = refl

brisbaneFossilReported :
  reportedPercent brisbaneFossil ≡ 28
brisbaneFossilReported = refl

antalyaFossilReported :
  reportedPercent antalyaFossil ≡ 33
antalyaFossilReported = refl

-- Arithmetic difference between two report-specific rounded scores
-- is real as an arithmetic statement, but NOT a harmonized time-
-- series change in the same commitment, nor a causal trend.
publishedFossilScoreDifference :
  reportedPercent brisbaneFossil + 5
  ≡ reportedPercent antalyaFossil
publishedFossilScoreDifference = refl

differentComplianceStudyPopulations :
  scoringPopulation brisbaneFinal2014
  ≡ scoringPopulation antalyaFinal2015 → ⊥
differentComplianceStudyPopulations ()

noReportedClimateCausalInfluence :
  IndependentEvaluation.causalGCCOrExxonEffectMeasured
    (study brisbaneFinal2014) ≡ false
noReportedClimateCausalInfluence = refl

notAnEmissionsOutcome :
  IndependentEvaluation.emissionsPerformanceMeasured
    (study antalyaFinal2015) ≡ false
notAnEmissionsOutcome = refl

-- Source-reported selected commitments remain genuine observations
-- under the original scoring protocol. Any change in G20 compliance
-- or actual emissions must join original item-level decisions,
-- member data, changed commitment terms and the reporting periods.
