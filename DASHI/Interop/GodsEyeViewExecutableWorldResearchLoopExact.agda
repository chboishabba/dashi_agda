module DASHI.Interop.GodsEyeViewExecutableWorldResearchLoopExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.GodsEyeViewDiagnosisDrivenActivistRollupExact as Diagnosis
import DASHI.Interop.GodsEyeViewHighestAlphaObservationChoiceExact as Alpha
import DASHI.Interop.GodsEyeViewPublicInterestWorldResidualExact as Public
import DASHI.Core.EmpiricalSourceDiligenceAdmissionExact as Diligence

------------------------------------------------------------------------
-- EXECUTABLE WORLD-RESEARCH RETURN LOOP
--
-- Existing owners already provide:
--   concern -> residual -> candidate -> highest-alpha admitted observation.
-- This owner adds the missing return transition after bounded acquisition and
-- assessment.  Acquisition itself never pays a prerequisite.
------------------------------------------------------------------------

data ObservationReturnDisposition : Set where
  payPrerequisite : ObservationReturnDisposition
  keepOpen : ObservationReturnDisposition
  splitDiagnosis : ObservationReturnDisposition
  reactivateDiagnosis : ObservationReturnDisposition

record ObservationAssessmentShape : Set where
  constructor observation-assessment-shape
  field
    sameObjectResolved : Bool
    sourceSupportResolved : Bool
    prerequisitePaid : Bool
    competingExplanationSplitRequired : Bool
    priorClosedConclusionDefeated : Bool

open ObservationAssessmentShape public

classifyObservationReturn : ObservationAssessmentShape → ObservationReturnDisposition
classifyObservationReturn a with priorClosedConclusionDefeated a
... | true = reactivateDiagnosis
... | false with competingExplanationSplitRequired a
...   | true = splitDiagnosis
...   | false with prerequisitePaid a
...     | true = payPrerequisite
...     | false = keepOpen

------------------------------------------------------------------------
-- Full assessed acquisition stays bound to the exact selected candidate.
------------------------------------------------------------------------

record AssessedObservationResult : Set₁ where
  constructor assessed-observation-result
  field
    selectedCandidate : Alpha.HighestAlphaCandidate
    acquisitionReceiptReference : String
    acquiredEvidenceReference : String
    sourceInspectionReference : String
    sourceDiligence : Diligence.SourceDiligence
    sameObjectAssessmentReference : String
    temporalAssessmentReference : String
    coverageAssessmentReference : String
    contradictionAssessmentReference : String
    authorityAssessmentReference : String
    applicabilityAssessmentReference : String
    assessmentShape : ObservationAssessmentShape
    assessmentReference : String

open AssessedObservationResult public

disposition : AssessedObservationResult → ObservationReturnDisposition
disposition r = classifyObservationReturn (assessmentShape r)

------------------------------------------------------------------------
-- Recomputed concern preserves the previous diagnosis and exact residual.
------------------------------------------------------------------------

record RecomputedWorldConcern : Set₁ where
  constructor recomputed-world-concern
  field
    priorConcern : Diagnosis.DiagnosedWorldConcern
    priorResidual : Public.WorldQueryResidual
    assessedResult : AssessedObservationResult
    returnDisposition : ObservationReturnDisposition
    returnDispositionMatches : returnDisposition ≡ disposition assessedResult
    updatedEvidenceReference : String
    updatedCompetingExplanationsReference : String
    updatedCausalDistinctionsReference : String
    updatedFirstMissingPrerequisiteReference : String
    updatedCandidateProducerReference : String
    updatedSourceDiligenceReference : String
    updatedAffectedInterestReference : String
    updatedRemedyOrAccountabilityReference : String
    provenancePreservedReference : String
    recomputationReference : String

open RecomputedWorldConcern public

------------------------------------------------------------------------
-- The return object cannot be constructed merely from an acquisition receipt.
------------------------------------------------------------------------

data AcquisitionReceiptAutomaticallyPaysPrerequisite : Set where
data SourceInspectionAutomaticallyCreatesAuthority : Set where
data PaidPrerequisiteAutomaticallyClosesWholeConcern : Set where
data SplitDiagnosisMayErasePriorEvidence : Set where
data ReactivationErasesPriorClosureHistory : Set where

acquisitionDoesNotAutomaticallyPay :
  AcquisitionReceiptAutomaticallyPaysPrerequisite → ⊥
acquisitionDoesNotAutomaticallyPay ()

inspectionDoesNotCreateAuthority : SourceInspectionAutomaticallyCreatesAuthority → ⊥
inspectionDoesNotCreateAuthority ()

paymentDoesNotCloseWholeConcern : PaidPrerequisiteAutomaticallyClosesWholeConcern → ⊥
paymentDoesNotCloseWholeConcern ()

splitPreservesPriorEvidence : SplitDiagnosisMayErasePriorEvidence → ⊥
splitPreservesPriorEvidence ()

reactivationPreservesClosureHistory : ReactivationErasesPriorClosureHistory → ⊥
reactivationPreservesClosureHistory ()

------------------------------------------------------------------------
-- Three concrete cross-domain fixture shapes.
-- These are executable disposition regressions, not empirical findings.
------------------------------------------------------------------------

data WorldResearchFixtureDomain : Set where
  predictionMarketAbuse : WorldResearchFixtureDomain
  lesAgroecology : WorldResearchFixtureDomain
  internationalAccountability : WorldResearchFixtureDomain

record WorldResearchLoopFixture : Set where
  constructor world-research-loop-fixture
  field
    domain : WorldResearchFixtureDomain
    concernReference : String
    firstMissingPrerequisiteReference : String
    selectedObservationReference : String
    sourceOrEvidenceReference : String
    shape : ObservationAssessmentShape
    expectedDisposition : ObservationReturnDisposition
    dispositionRegression : classifyObservationReturn shape ≡ expectedDisposition
    boundaryReference : String

open WorldResearchLoopFixture public

marketIdentityStillOpenFixture : WorldResearchLoopFixture
marketIdentityStillOpenFixture = world-research-loop-fixture
  predictionMarketAbuse
  "abnormal pre-event prediction-market trading"
  "trader/entity identity and information-access basis"
  "pull bounded public venue trades/orderbook plus public on-chain funding history"
  "public market/chain observations; wallet cluster is not person identity"
  (observation-assessment-shape false true false false false)
  keepOpen refl
  "anomaly != MNPI; wallet cluster != person; MNPI != duty/liability"

lesCompetingMechanismSplitFixture : WorldResearchLoopFixture
lesCompetingMechanismSplitFixture = world-research-loop-fixture
  lesAgroecology
  "orchard canopy stress visible in Earth-observation surface"
  "distinguish water stress from nutrient/pest/disease mechanism"
  "lawful field calibration / grower observation after remote screening"
  "remote observation plus local field evidence; intervention authority remains separate"
  (observation-assessment-shape true true false true false)
  splitDiagnosis refl
  "remote sensing != whole LES planning state; Country/community authority remains independent"

internationalLawReactivationFixture : WorldResearchLoopFixture
internationalLawReactivationFixture = world-research-loop-fixture
  internationalAccountability
  "contested international-law characterization of a state operation"
  "current primary legal/party/institutional authority and contrary position"
  "inspect exact primary filing/UN/court/state source and adverse source"
  "new contrary or superseding authority can defeat an earlier provisional closure"
  (observation-assessment-shape true true false false true)
  reactivateDiagnosis refl
  "UN statement, party pleading and court judgment remain distinct authority roles"

sourceSupportPaymentFixture : WorldResearchLoopFixture
sourceSupportPaymentFixture = world-research-loop-fixture
  internationalAccountability
  "bounded proposition lacking exact primary-source support"
  "exact source span on the same object and time"
  "inspect the primary source and attach exact locator"
  "same source/object/span validated; downstream authority still separate"
  (observation-assessment-shape true true true false false)
  payPrerequisite refl
  "paying source support advances only that prerequisite; whole concern is recomputed"

record ExecutableWorldResearchLoopBoundary : Set where
  constructor executable-world-research-loop-boundary
  field
    acquisitionEqualsPayment : Bool
    acquisitionEqualsPaymentIsFalse : acquisitionEqualsPayment ≡ false
    assessmentCanSplitDiagnosis : Bool
    assessmentCanSplitDiagnosisIsTrue : assessmentCanSplitDiagnosis ≡ true
    newEvidenceCanReactivatePriorClosure : Bool
    newEvidenceCanReactivatePriorClosureIsTrue : newEvidenceCanReactivatePriorClosure ≡ true
    paidPrerequisiteRequiresRecomputation : Bool
    paidPrerequisiteRequiresRecomputationIsTrue : paidPrerequisiteRequiresRecomputation ≡ true
    priorProvenanceMustSurvive : Bool
    priorProvenanceMustSurviveIsTrue : priorProvenanceMustSurvive ≡ true

canonicalExecutableWorldResearchLoopBoundary : ExecutableWorldResearchLoopBoundary
canonicalExecutableWorldResearchLoopBoundary =
  executable-world-research-loop-boundary false refl true refl true refl true refl true refl
