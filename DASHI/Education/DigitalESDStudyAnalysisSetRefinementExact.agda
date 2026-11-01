module DASHI.Education.DigitalESDStudyAnalysisSetRefinementExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDStudyClaimCeilingExact as Ceiling
import DASHI.Education.DigitalESDStudyClaimPilotExtensionExact as Extension
import DASHI.Education.DigitalESDStudyClaimQuantitativePilotExact as Quant
import DASHI.Education.DigitalESDRandomizedCausalAcquisitionExact as RCT

------------------------------------------------------------------------
-- STUDY ANALYSIS-SET REFINEMENT
--
-- Source-driven least-coordinate repair. Multiple heterogeneous pilot sources
-- demonstrate that a study-level sample size and one primary analysisN cannot
-- represent every inferential/qualitative analysis set without loss:
--
--   Fishlock: registered n=40; survey n=14; focus-group n=5.
--   Braßler: stated N=409; inferential analysis denominator remains unresolved.
--   Green/Molloy/Duggan: validated randomized n=106; reported contrasts use
--     outcome-specific post-randomization analysis sets such as 24 vs 27.
--
-- This owner therefore adds an optional adjunct list of analysis-set receipts.
-- It does NOT replace StudyClaimProfile and does not make multi-set structure a
-- universal requirement for studies whose one analysisN is sufficient.
------------------------------------------------------------------------

record AnalysisSetReceipt : Set where
  constructor analysis-set-receipt
  field
    analysisKey : String
    analysisN : Ceiling.ReportedNat
    sourceLocator : String
    outcomeOrMethod : String
    inclusionExclusionReference : String
    comparatorOrRoleReference : String
    interpretationBoundary : String

open AnalysisSetReceipt public

record StudyAnalysisSetProfile : Set where
  constructor study-analysis-set-profile
  field
    parentStudy : Ceiling.StudyClaimProfile
    analysisSets : List AnalysisSetReceipt
    refinementReason : String
    singleStudyLevelAnalysisNIsSufficient : Bool
    singleStudyLevelAnalysisNIsSufficientIsFalse :
      singleStudyLevelAnalysisNIsSufficient ≡ false

open StudyAnalysisSetProfile public

------------------------------------------------------------------------
-- Fishlock: method-specific qualitative/quantitative slices.
------------------------------------------------------------------------

fishlockSurveySet : AnalysisSetReceipt
fishlockSurveySet = analysis-set-receipt
  "fishlock-survey"
  Extension.fishlockSurveyAnalysisN
  "10.1002/gch2.202300158; Results 3.1-3.2"
  "anonymous questionnaire"
  "14 questionnaire respondents from 40 registered students; no denominator is silently promoted to a study-wide response population"
  "descriptive survey percentages; no untreated comparator"
  "survey n=14 supports only the survey findings; it does not become the focus-group n, registered cohort n, population prevalence or intervention effect"

fishlockFocusGroupSet : AnalysisSetReceipt
fishlockFocusGroupSet = analysis-set-receipt
  "fishlock-focus-group"
  Extension.fishlockFocusGroupAnalysisN
  "10.1002/gch2.202300158; focus-group analysis"
  "qualitative focus group"
  "5 focus-group participants retained as a distinct analysis slice"
  "qualitative participant accounts; no experimental comparator"
  "focus-group n=5 supports situated qualitative interpretation only and cannot be fused with survey n=14 into a fabricated single analysis n"

fishlockAnalysisSets : StudyAnalysisSetProfile
fishlockAnalysisSets = study-analysis-set-profile
  Extension.fishlockPilotProfile
  (fishlockSurveySet ∷ fishlockFocusGroupSet ∷ [])
  "one educational pilot contains distinct questionnaire and focus-group analysis populations"
  false refl

------------------------------------------------------------------------
-- Braßler: study sample is known while fitted-model analysis n is not.
------------------------------------------------------------------------

brasslerDeclaredStudySet : AnalysisSetReceipt
brasslerDeclaredStudySet = analysis-set-receipt
  "brassler-declared-study-sample"
  (Ceiling.explicitlyReportedNat 409
    "study sample: 83 OER-production students + 326 control-group students")
  "10.3390/su16041674; Sample and Design 5.1"
  "declared study sample"
  "publisher article reports N=409"
  "83 OER-production and 326 same-cohort control students"
  "declared N is retained as the study population statement and is not automatically equated with the inferential repeated-measures analysis set"

brasslerInferentialSet : AnalysisSetReceipt
brasslerInferentialSet = analysis-set-receipt
  "brassler-repeated-measures-analysis"
  (Ceiling.natNotReported
    "article reports N=409 but repeated-measures ANOVA F(1,191); exact inferential analysis n is not reconstructed from degrees of freedom")
  "10.3390/su16041674; Results 6"
  "repeated-measures Time and Time×Group model"
  "visible primary text does not currently pay the missing-data/analysis-set bridge from N=409 to denominator df=191"
  "OER-production versus same-cohort control condition"
  "reported F, p and partial eta-squared statistics remain usable as source-reported bounded contrasts while exact analysis n remains acquisition debt"

brasslerAnalysisSets : StudyAnalysisSetProfile
brasslerAnalysisSets = study-analysis-set-profile
  Quant.brasslerPilotProfile
  (brasslerDeclaredStudySet ∷ brasslerInferentialSet ∷ [])
  "declared study N and inferential model analysis set cannot be treated as identical from the currently acquired source text"
  false refl

------------------------------------------------------------------------
-- Green/Molloy/Duggan: randomized carrier plus outcome-local analyzed sets.
------------------------------------------------------------------------

greenValidatedRandomizedSet : AnalysisSetReceipt
greenValidatedRandomizedSet = analysis-set-receipt
  "green-validated-randomized-carrier"
  (Ceiling.explicitlyReportedNat 106
    "complete validated datasets before random assignment analysis")
  "10.3390/su14010394; Methods 4.6"
  "validated randomized participant carrier"
  "227 signup funnel -> 106 complete validated datasets; full randomized groups control 28, systems 26, simulation 24, combined 28"
  "2x2 randomized factorial assignment"
  "this carrier records the randomized study population after pre-analysis validation; it does not imply every later outcome analysis retains all 106 records"

greenQuiz1SimulationSet : AnalysisSetReceipt
greenQuiz1SimulationSet = analysis-set-receipt
  "green-quiz1-simulation"
  (Ceiling.explicitlyReportedNat 24 "simulation group in Quiz-1 contrast")
  "10.3390/su14010394; Results / Table 6"
  "Quiz-1 immediate sustainability-score analysis"
  "simulation group retains 24 records"
  "simulation-only factor group"
  "n=24 belongs to this outcome/group slice; it is not the total trial analysis n"

greenQuiz1ControlSet : AnalysisSetReceipt
greenQuiz1ControlSet = analysis-set-receipt
  "green-quiz1-control-analyzed"
  (Ceiling.explicitlyReportedNat 27
    "analyzed control group after one Quiz-1 control outlier removal")
  "10.3390/su14010394; Results / Table 6"
  "Quiz-1 immediate sustainability-score analysis"
  "full randomized control n=28; one control outlier removed before the reported inferential comparison"
  "control group comparator"
  "post-randomization exclusion means analyzed control n=27 must remain distinct from randomized control n=28; randomization alone does not adjudicate the exclusion"

greenQuiz2SimulationSet : AnalysisSetReceipt
greenQuiz2SimulationSet = analysis-set-receipt
  "green-quiz2-simulation-analyzed"
  (Ceiling.explicitlyReportedNat 23
    "simulation group in reported Quiz-2 transfer contrast")
  "10.3390/su14010394; Quiz-2 results"
  "near-term transfer/fisheries quiz analysis"
  "reported transfer analysis removes non-engaged records using page analytics"
  "simulation group"
  "analysis-local n and exclusion rationale remain part of the transfer-result receipt rather than being projected back onto Quiz 1 or the whole trial"

greenQuiz2ControlSet : AnalysisSetReceipt
greenQuiz2ControlSet = analysis-set-receipt
  "green-quiz2-control-analyzed"
  (Ceiling.explicitlyReportedNat 26
    "control group in reported Quiz-2 transfer contrast")
  "10.3390/su14010394; Quiz-2 results"
  "near-term transfer/fisheries quiz analysis"
  "source removes an extreme control outlier and non-engaged datasets before this reported contrast"
  "control group comparator"
  "n=26 is an outcome-local analyzed control set and does not replace the randomized control carrier n=28"

greenAnalysisSets : StudyAnalysisSetProfile
greenAnalysisSets = study-analysis-set-profile
  RCT.greenMolloyDugganPilotProfile
  ( greenValidatedRandomizedSet
  ∷ greenQuiz1SimulationSet
  ∷ greenQuiz1ControlSet
  ∷ greenQuiz2SimulationSet
  ∷ greenQuiz2ControlSet
  ∷ [] )
  "randomized carrier and reported outcome-local analysis sets differ because exclusions are outcome/analysis specific"
  false refl

------------------------------------------------------------------------
-- Promotion firewalls and review boundary.
------------------------------------------------------------------------

data OnePaperDeterminesOneAnalysisSet : Set where
data StudyNDeterminesEveryAnalysisN : Set where
data DegreesOfFreedomDeterminesAnalysisNWithoutReceipt : Set where
data RandomizedCarrierMakesEveryPostRandomizationExclusionAdmissible : Set where

onePaperDoesNotDetermineOneAnalysisSet : OnePaperDeterminesOneAnalysisSet → ⊥
onePaperDoesNotDetermineOneAnalysisSet ()

studyNDoesNotDetermineEveryAnalysisN : StudyNDeterminesEveryAnalysisN → ⊥
studyNDoesNotDetermineEveryAnalysisN ()

degreesOfFreedomDoesNotDetermineAnalysisNWithoutReceipt :
  DegreesOfFreedomDeterminesAnalysisNWithoutReceipt → ⊥
degreesOfFreedomDoesNotDetermineAnalysisNWithoutReceipt ()

randomizedCarrierDoesNotMakeEveryPostRandomizationExclusionAdmissible :
  RandomizedCarrierMakesEveryPostRandomizationExclusionAdmissible → ⊥
randomizedCarrierDoesNotMakeEveryPostRandomizationExclusionAdmissible ()

record AnalysisSetRefinementBoundary : Set where
  constructor analysis-set-refinement-boundary
  field
    onePaperMayHaveMultipleAnalysisSets : Bool
    onePaperMayHaveMultipleAnalysisSetsIsTrue :
      onePaperMayHaveMultipleAnalysisSets ≡ true
    baseStudyClaimProfileRetained : Bool
    baseStudyClaimProfileRetainedIsTrue : baseStudyClaimProfileRetained ≡ true
    refinementIsOptionalAndConsumerDriven : Bool
    refinementIsOptionalAndConsumerDrivenIsTrue :
      refinementIsOptionalAndConsumerDriven ≡ true
    sourceLocalAnalysisNsRetained : Bool
    sourceLocalAnalysisNsRetainedIsTrue : sourceLocalAnalysisNsRetained ≡ true
    missingAnalysisNMayBeDerivedFromDFWithoutReceipt : Bool
    missingAnalysisNMayBeDerivedFromDFWithoutReceiptIsFalse :
      missingAnalysisNMayBeDerivedFromDFWithoutReceipt ≡ false
    randomizationAutomaticallyAdjudicatesAllAnalysisExclusions : Bool
    randomizationAutomaticallyAdjudicatesAllAnalysisExclusionsIsFalse :
      randomizationAutomaticallyAdjudicatesAllAnalysisExclusions ≡ false

open AnalysisSetRefinementBoundary public

canonicalAnalysisSetRefinementBoundary : AnalysisSetRefinementBoundary
canonicalAnalysisSetRefinementBoundary =
  analysis-set-refinement-boundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl

analysisSetRefinementReading : String
analysisSetRefinementReading =
  "Repeated source ingestion demonstrated a concrete recurring residual: one study can contain several method-, outcome-, group- or exclusion-specific analysis sets. The base StudyClaimProfile remains canonical and sufficient for simple cases; this optional refinement retains exact local analysis Ns and inclusion/exclusion provenance where a single study-level analysisN would erase consumer-relevant distinctions. Study N does not determine every analysis N, degrees of freedom do not backfill a missing analysis N without a same-object derivation receipt, and randomized assignment does not automatically adjudicate post-randomization exclusions."
