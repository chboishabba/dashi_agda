module DASHI.Education.DigitalESDAdaptiveScreeningControllerRegression where

open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDAdaptiveScreeningControllerExact as Adaptive

candidateAssessmentCannotDecide :
  Adaptive.CandidateAssessmentCreatesScreeningDecision → ⊥
candidateAssessmentCannotDecide =
  Adaptive.candidateAssessmentCannotCreateScreeningDecision

selectorCannotDecide :
  Adaptive.SelectorCreatesScreeningDecision → ⊥
selectorCannotDecide =
  Adaptive.selectorCannotCreateScreeningDecision

unselectedRecordsRemainInDenominator :
  Adaptive.UnselectedRecordMayLeaveDenominator → ⊥
unselectedRecordsRemainInDenominator =
  Adaptive.unselectedRecordCannotLeaveDenominator

fibreHypothesisCannotBecomeStudyIdentity :
  Adaptive.FibreHypothesisCreatesStudyIdentity → ⊥
fibreHypothesisCannotBecomeStudyIdentity =
  Adaptive.fibreHypothesisCannotCreateStudyIdentity

missingAbstractCannotBecomeExclusion :
  Adaptive.MissingAbstractMeansExclude → ⊥
missingAbstractCannotBecomeExclusion =
  Adaptive.missingAbstractDoesNotMeanExclude

screeningCannotCreateAuditAdmission :
  Adaptive.ScreeningDecisionCreatesAuditAdmission → ⊥
screeningCannotCreateAuditAdmission =
  Adaptive.screeningDecisionCannotCreateAuditAdmission

slrReviewCannotCreateAuditAdmission :
  Adaptive.SLRReviewCreatesAuditAdmission → ⊥
slrReviewCannotCreateAuditAdmission =
  Adaptive.slrReviewCannotCreateAuditAdmission
