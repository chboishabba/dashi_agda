module DASHI.Education.DigitalESDAdaptiveScreeningProgrammeRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDAdaptiveScreeningProgrammeExact as P0

candidateAssessmentCannotCreateDecision :
  P0.CandidateAssessmentCreatesScreeningDecision → ⊥
candidateAssessmentCannotCreateDecision =
  P0.candidateAssessmentDoesNotCreateScreeningDecision

candidateAssessmentCannotExclude :
  P0.CandidateAssessmentCreatesExclusion → ⊥
candidateAssessmentCannotExclude =
  P0.candidateAssessmentDoesNotCreateExclusion

studyFamilyHypothesisCannotCreateStudyIdentity :
  P0.StudyFamilyHypothesisCreatesSameEmpiricalStudy → ⊥
studyFamilyHypothesisCannotCreateStudyIdentity =
  P0.studyFamilyHypothesisDoesNotCreateSameEmpiricalStudy

paretoPriorityCannotCreateDecision :
  P0.ParetoPriorityCreatesScreeningDecision → ⊥
paretoPriorityCannotCreateDecision =
  P0.paretoPriorityDoesNotCreateScreeningDecision

unreviewedCannotDisappear :
  P0.UnreviewedRecordMayLeaveDenominator → ⊥
unreviewedCannotDisappear =
  P0.unreviewedRecordDoesNotLeaveDenominator

missingAbstractCannotBecomeAutomaticExclude :
  P0.MissingAbstractCreatesAutomaticExclusion → ⊥
missingAbstractCannotBecomeAutomaticExclude =
  P0.missingAbstractDoesNotCreateAutomaticExclusion

calibrationCannotCreateTruth :
  P0.CalibrationEstimateCreatesSourceTruth → ⊥
calibrationCannotCreateTruth =
  P0.calibrationEstimateDoesNotCreateSourceTruth

fullTextRetrievalCannotCreateAdmission :
  P0.FullTextRetrievalCreatesSourceAuditAdmission → ⊥
fullTextRetrievalCannotCreateAdmission =
  P0.fullTextRetrievalDoesNotCreateSourceAuditAdmission

p0aUsesAuthoritativeLedger :
  P0.usesExistingScreeningLedger P0.canonicalAdaptiveScreeningBoundary ≡ true
p0aUsesAuthoritativeLedger = refl

p0fUsesRepoPareto :
  P0.usesRepoNativePareto P0.canonicalAdaptiveScreeningBoundary ≡ true
p0fUsesRepoPareto = refl

p0gKeepsSLRDownstream :
  P0.slrOnlyAfterRetainedOrProbable P0.canonicalAdaptiveScreeningBoundary ≡ true
p0gKeepsSLRDownstream = refl
