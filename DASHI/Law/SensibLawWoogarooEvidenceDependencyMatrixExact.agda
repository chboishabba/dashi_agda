module DASHI.Law.SensibLawWoogarooEvidenceDependencyMatrixExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.EvidenceProvenanceDependencyDagExact as Provenance
import DASHI.Law.SensibLawWoogarooS102LikelySignificantDetrimentalEffectCaseExact as S102
import DASHI.Law.SensibLawWoogarooS13EssentialityStressTestExact as S13
import DASHI.Law.SensibLawWoogarooEPBC43BHistoricalClearingApplicabilityExact as S43B

------------------------------------------------------------------------
-- WOOGAROO EVIDENCE DEPENDENCY MATRIX
--
-- Concrete source-dependency calculation for the live preservation case.
-- Multiple reports, maps, approvals or later summaries are not counted as
-- independent evidence merely because they are separate documents.  The
-- consumer reopens provenance and same-object identity at the exact proposition
-- it needs to pay.
------------------------------------------------------------------------

data WoogarooCarrier : Set where
  shg2019Ecology
  shgFederalImpactAssessment
  epbcReferral2019_8575
  councilNegotiatedDecision9281
  approvedPlanA12705838
  currentExecutionRecords
  qldKoalaStatusRecord
  ncaCurrentAct
  epbcCurrentAct
  currentEcologicalExpertOpinion
  historicalAerialSeries
  viablePopulationStudy : WoogarooCarrier

data DependencyRelation : Set where
  sameUnderlyingEcology
  derivesFrom
  legallyIndependentSource
  observationallyIndependentSource
  sameProjectDifferentConsumer
  identityUnresolved : DependencyRelation

record DependencyCell : Set where
  constructor dependency-cell
  field
    left right : WoogarooCarrier
    relation : DependencyRelation
    paid : Bool
    receipt : String
    consequence : String

open DependencyCell public

shgEcologyToFederal : DependencyCell
shgEcologyToFederal = dependency-cell
  shg2019Ecology shgFederalImpactAssessment sameUnderlyingEcology true
  "Both propositions are carried by proponent-side Saunders Havill Group ecology for the Springview/Woogaroo project."
  "Habitat score, Koala occurrence/connectivity, fragmentation and the federal significant-impact conclusion are not independent corroborators merely because they appear as multiple propositions or documents."

federalToReferral : DependencyCell
federalToReferral = dependency-cell
  shgFederalImpactAssessment epbcReferral2019_8575 derivesFrom true
  "The referral/assessment lane uses project ecology generated for the same development action."
  "A referral record can independently establish regulatory history, but it does not create a second independent ecological observation stream."

councilDecisionToPlan : DependencyCell
councilDecisionToPlan = dependency-cell
  councilNegotiatedDecision9281 approvedPlanA12705838 sameProjectDifferentConsumer true
  "The negotiated decision and A12705838 approved plan belong to the same 9281/2024/OW approval package but pay different consumers: legal authorisation/conditions versus plan-scale geometry."
  "Same approval package does not mean the legal decision and geometry are interchangeable; exact plan identity is still required for spatial claims."

projectEcologyToCouncil : DependencyCell
projectEcologyToCouncil = dependency-cell
  shg2019Ecology councilNegotiatedDecision9281 sameProjectDifferentConsumer true
  "Both concern the Springview/Woogaroo development lineage, but one is ecological evidence and the other is a later governmental approval record."
  "Council approval is institutionally distinct from SHG ecological authorship, yet it does not independently replicate the historical Koala observations."

qldStatusIndependent : DependencyCell
qldStatusIndependent = dependency-cell
  qldKoalaStatusRecord shg2019Ecology legallyIndependentSource true
  "Queensland threatened-species listing/status is an official government source independent of the proponent ecology."
  "It independently pays threatened-wildlife status, not project exposure, essentiality or likely significant detrimental effect."

ncaIndependent : DependencyCell
ncaIndependent = dependency-cell
  ncaCurrentAct shg2019Ecology legallyIndependentSource true
  "The current Nature Conservation Act is a primary statutory source independent of the project evidence."
  "It pays the statutory consumer only; legal text is not ecological corroboration."

currentExpertUnpaid : DependencyCell
currentExpertUnpaid = dependency-cell
  currentEcologicalExpertOpinion shg2019Ecology observationallyIndependentSource false
  "Current independent project-specific ecological opinions are now source-paid through the 12 March 2026 QCC and QUT EPBC 2019/8575 submissions, but no independent ecological opinion explicitly applies the Queensland s 12/s 102 wording to the current project state."
  "Generic current-project ecological opposition is no longer the residual; the unpaid consumer is the direct NCA s 102 threatening-process / likely-significant-detrimental-effect application."

executionJoinUnpaid : DependencyCell
executionJoinUnpaid = dependency-cell
  currentExecutionRecords approvedPlanA12705838 identityUnresolved false
  "Condition 6(a), prestart, fauna/arborist and commencement records have not yet been joined to the exact approved plan/time state."
  "Urgency and actual execution remain open even though approval geometry is known."

populationJoinUnpaid : DependencyCell
populationJoinUnpaid = dependency-cell
  viablePopulationStudy shg2019Ecology identityUnresolved false
  "Regional SEQ population structure, Ipswich population context and current Woogaroo resident-koala/connectivity evidence are now source-paid; the exact Springview/Woogaroo resident animals have not yet been joined to an independently characterised genetic/demographic cluster or subpopulation."
  "s 13 essentiality remains open because the exact site-to-population identity and without-site viability counterfactual are still unpaid."

historicalS43BUnpaid : DependencyCell
historicalS43BUnpaid = dependency-cell
  historicalAerialSeries epbcCurrentAct identityUnresolved false
  "Historical aerial/canopy evidence is not yet a complete 15-year clearing-history proof for an exact action, and no current s 43B reliance document has been located."
  "The s 43B lane stays conditional rather than competing with the live Part 9 merits route."

------------------------------------------------------------------------
-- Consumer-specific independence accounting.
-- Counts remain the original matrix bookkeeping classes.  Newly acquired
-- source multiplicity is tracked in the population/connectivity snowball owner
-- rather than inflating these historical counts without a fresh quotient pass.
------------------------------------------------------------------------

data WoogarooConsumer : Set where
  threatenedWildlifeStatus
  projectExposure
  likelySignificantDetrimentalEffect
  statutoryEssentiality
  currentExecutionUrgency
  s43BApplicability : WoogarooConsumer

record ConsumerDependencyState : Set where
  constructor consumer-dependency-state
  field
    consumer : WoogarooConsumer
    sourceMultiplicity : Nat
    independentUpstreamCarriers : Nat
    sameObjectJoinPaid : Bool
    causalOrLegalPromotionPaid : Bool
    firstUnpaid : String

open ConsumerDependencyState public

s102DependencyState : ConsumerDependencyState
s102DependencyState = consumer-dependency-state
  likelySignificantDetrimentalEffect
  6 3 true false
  "Apply the now-located current independent project-specific ecological evidence to the exact Queensland s 102 wording, preferably through an independent ecological opinion that explicitly addresses the exact approved clearing/earthworks threatening process and likely significant detrimental effect."

s13DependencyState : ConsumerDependencyState
s13DependencyState = consumer-dependency-state
  statutoryEssentiality
  5 3 false false
  "Join the Springview/Woogaroo resident koalas to an independently characterised SEQ genetic/demographic cluster or subpopulation, then quantify the without-site persistence/movement/breeding/resource-access counterfactual."

executionDependencyState : ConsumerDependencyState
executionDependencyState = consumer-dependency-state
  currentExecutionUrgency
  2 1 false false
  "Join current Condition 6(a)/prestart/commencement records to the exact A12705838 approved geometry and time state."

s43BDependencyState : ConsumerDependencyState
s43BDependencyState = consumer-dependency-state
  s43BApplicability
  3 2 false false
  "First locate an actual s 43B reliance record; only then reconstruct exact-action pre-2000 use and 15-year clearing history."

------------------------------------------------------------------------
-- Cross-lane status reuse.  This owner does not promote the open conclusions.
------------------------------------------------------------------------

s102Current : S102.S102CaseState
s102Current = S102.currentS102CaseState

s13Current : S13.S13StressTest
s13Current = S13.currentS13StressTest

s43BCurrent : S43B.CurrentS43BConclusion
s43BCurrent = S43B.currentS43BConclusion

provenanceBoundary : Provenance.ProvenanceDagBoundary
provenanceBoundary = Provenance.canonicalProvenanceDagBoundary

------------------------------------------------------------------------
-- WrongType boundaries.
------------------------------------------------------------------------

data MultipleSHGClaimsMeanIndependentCorroboration : Set where
data SameProjectMeansSameObservation : Set where
data IndependentStatuteMeansIndependentEcology : Set where
data ApprovalGeometryMeansExecution : Set where
data HistoricalAerialMeansS43BReliance : Set where

multipleSHGClaimsDoNotCreateIndependence : MultipleSHGClaimsMeanIndependentCorroboration → ⊥
multipleSHGClaimsDoNotCreateIndependence ()

sameProjectDoesNotMeanSameObservation : SameProjectMeansSameObservation → ⊥
sameProjectDoesNotMeanSameObservation ()

independentStatuteDoesNotCreateEcologicalCorroboration : IndependentStatuteMeansIndependentEcology → ⊥
independentStatuteDoesNotCreateEcologicalCorroboration ()

approvalGeometryDoesNotCreateExecution : ApprovalGeometryMeansExecution → ⊥
approvalGeometryDoesNotCreateExecution ()

historicalAerialDoesNotCreateS43BReliance : HistoricalAerialMeansS43BReliance → ⊥
historicalAerialDoesNotCreateS43BReliance ()
