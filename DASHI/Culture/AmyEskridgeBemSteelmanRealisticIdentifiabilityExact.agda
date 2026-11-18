module DASHI.Culture.AmyEskridgeBemSteelmanRealisticIdentifiabilityExact where

-- MAXIMUM-CUT: what Bem's reported numbers DO and DO NOT force.
-- This is a logical identifiability theorem, not a finding that
-- Bem used selective analysis, manipulated data, or falsified results.
--
-- Original: Daryl J. Bem, JPSP 2011, DOI 10.1037/a0021524.
-- Reported comparison: 53.07% of 1560 erotic trials in Bem Experiment 1
-- (published percentage may not be an integer raw count: the reported
-- percentage is used only as the reported comparison).
-- Replication: Kekecs et al 2023, Royal Society Open Science,
-- DOI 10.1098/rsos.191375, 49.89% of 37836 erotic trials.
-- Source: https://pmc.ncbi.nlm.nih.gov/articles/PMC9890107/
-- Under the realistic null, any finite sequence of 0/1 Bernoulli
-- guesses has positive probability. "Could occur" != "did occur".
-- The speaker's assertion of precognition has no earned mechanism receipt.
--
-- Reuses pre-existing anomaly evidence owners. Transparent Psi cannot
-- prove any particular *historical* analytic fault from percentages alone.
-- TODO when original participant-level data & protocol provenance are
-- inspected: separate pre-registered, analytic-choice and exclusion witnesses.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Core.Prelude using (⊥)
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Governance.AnomalousPhenomenonTemporalEvidenceTrajectoriesExact as Trajectory
import DASHI.Culture.AmyEskridgeVideoTemporalForecastAndPsiMaxCutExact as Psi
import DASHI.Culture.AmyEskridgeVideoClaimProducerWeldExact as Video

-- Opposing published source families, authors retained:
-- original 2015 paper released version 2 in January 2016.
-- These sources CANNOT be counted as independent confirmation of an
-- experiment merely by appearing in a meta-analysis or a critique.
steelman90StudyMeta : Attribution.AttributedSource
steelman90StudyMeta = Attribution.mkDOISource
  "Daryl Bem; Patrizio Tressoldi; Thomas Rabeyron; Michael Duggan"
  "Feeling the future: A meta-analysis of 90 experiments on the anomalous anticipation of random future events"
  "F1000Research 4:1188, first published 2015, version 2 Jan 2016"
  "2016"
  "10.12688/f1000research.7177.2"
  "https://f1000research.com/articles/4-1188/v2"
  Attribution.academicArticleSource
  "Proponent analysis reports a positive small aggregate signal; selection, dependence, study-quality interactions and replicability remain independent gates"
  Attribution.publicAttribution

criticalRouderMorey2011 : Attribution.AttributedSource
criticalRouderMorey2011 = Attribution.mkDOISource
  "Jeffrey N. Rouder; Richard D. Morey"
  "A Bayes factor meta-analysis of Bem's ESP claim"
  "Psychonomic Bulletin & Review 18:682-689"
  "2011"
  "10.3758/s13423-011-0088-7"
  "https://pubmed.ncbi.nlm.nih.gov/21573926/"
  Attribution.academicArticleSource
  "Alternative statistical interpretation of Bem's evidence; does not establish intentional analysis selection or misconduct"
  Attribution.publicAttribution

data CompetingExplanation : Set where
  prospectiveStableEffect : CompetingExplanation
  finiteNullFluctuation : CompetingExplanation
  analyticBranchSelection : CompetingExplanation
  protocolModerator : CompetingExplanation

-- Keeping the same OBSERVATION despite a different hidden explanation
-- is an intentional identifiability counterexample.
record ReportedExp1 : Set where
  constructor report
  field
    reportedBasisPoints : Nat
    reportedTrialCount : Nat
open ReportedExp1 public

publicExperimentOneReport : ReportedExp1
publicExperimentOneReport = report 5307 1560

record AdmissibleInterpretation : Set where
  constructor interpretation
  field
    observed : ReportedExp1
    hypothesis : CompetingExplanation
open AdmissibleInterpretation public

strongestSteelman : AdmissibleInterpretation
strongestSteelman = interpretation
  publicExperimentOneReport
  prospectiveStableEffect

realisticNull : AdmissibleInterpretation
realisticNull = interpretation
  publicExperimentOneReport
  finiteNullFluctuation

analyticFlexibilityScenario : AdmissibleInterpretation
analyticFlexibilityScenario = interpretation
  publicExperimentOneReport
  analyticBranchSelection

moderatorScenario : AdmissibleInterpretation
moderatorScenario = interpretation
  publicExperimentOneReport
  protocolModerator

sameReportedRate :
  reportedBasisPoints (observed strongestSteelman)
    ≡ reportedBasisPoints (observed realisticNull)
sameReportedRate = refl

sameReportedTrialCount :
  reportedTrialCount (observed strongestSteelman)
    ≡ reportedTrialCount (observed realisticNull)
sameReportedTrialCount = refl

-- Both candidate explanations make the identical supplied observation
-- possible in the source-epistemic model. Hence the observed aggregate
-- cannot entail a specific historical defect without NEW receipts.
data AnalyticFaultWitness : Set where
  documentedForkOrExclusion : AnalyticFaultWitness

-- This carrier intentionally contains zero members: the PRIMARY
-- SOURCE AUDIT has NOT established a historical fork or exclusion.
data PaidHistoricalAnalyticFault : Set where

noDocumentedHistoricalFaultInThisLedger :
  PaidHistoricalAnalyticFault → ⊥
noDocumentedHistoricalFaultInThisLedger ()

-- Selection bias can be constructed mathematically under an independently
-- specified selection rule; this DOES NOT say Bem used that rule.
selectMax : Nat → Nat → Nat
selectMax zero b = b
selectMax a zero = a
selectMax (suc a) (suc b) = suc (selectMax a b)

bestOfTwoAtLeastFirst : selectMax 5307 5000 ≡ 5307
bestOfTwoAtLeastFirst = refl

bestOfTwoAtLeastSecond : selectMax 5000 5307 ≡ 5307
bestOfTwoAtLeastSecond = refl

-- Negative-control: significance or published headline is not itself a
-- typed causal witness, so no constructor for this coercion exists.
data SignificantMeansResearcherUsedPHashing : Set where
data NullReplicationProvesOriginalFraud : Set where
data OneReplicationNullRefutesAllPsi : Set where
data NineExperimentsMustBeIndependent : Set where

noSignificanceToHistoricalPHashing :
  SignificantMeansResearcherUsedPHashing → ⊥
noSignificanceToHistoricalPHashing ()
noReplicationToFraud :
  NullReplicationProvesOriginalFraud → ⊥
noReplicationToFraud ()
noOneParadigmToAll :
  OneReplicationNullRefutesAllPsi → ⊥
noOneParadigmToAll ()
noAutomaticNineIndependence :
  NineExperimentsMustBeIndependent → ⊥
noAutomaticNineIndependence ()

-- Reuse the real current meta-evidence owners and video claim, not a
-- duplicate hypothesis engine. This does not close the physiology gate.
sameBemReplicationOwner :
  Trajectory.momentPhenomenon Trajectory.transparentPsi2025
    ≡ Trajectory.bemPrecognition
sameBemReplicationOwner = refl

sameReportedSource :
  Psi.originalBemExp1ReportedRate ≡ 5307
sameReportedSource = refl
