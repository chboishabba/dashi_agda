module DASHI.Education.DigitalESDAdaptiveScreeningExecutionRegression where

open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDAdaptiveScreeningExecutionExact as Exec

candidateRuntimeCannotDecide :
  Exec.RuntimeCandidateAssessmentCreatesScreeningDecision → ⊥
candidateRuntimeCannotDecide =
  Exec.runtimeCandidateAssessmentCannotCreateScreeningDecision

paretoRuntimeCannotDecide :
  Exec.RuntimeParetoSelectionCreatesScreeningDecision → ⊥
paretoRuntimeCannotDecide =
  Exec.runtimeParetoSelectionCannotCreateScreeningDecision

unselectedRuntimeCannotDropDenominator :
  Exec.RuntimeUnselectedRecordLeavesDenominator → ⊥
unselectedRuntimeCannotDropDenominator =
  Exec.runtimeUnselectedRecordCannotLeaveDenominator

familyRuntimeCannotCreateStudyIdentity :
  Exec.RuntimeFamilyHypothesisCreatesEmpiricalStudyIdentity → ⊥
familyRuntimeCannotCreateStudyIdentity =
  Exec.runtimeFamilyHypothesisCannotCreateEmpiricalStudyIdentity

missingAbstractRuntimeCannotExclude :
  Exec.RuntimeMissingAbstractCreatesExclusion → ⊥
missingAbstractRuntimeCannotExclude =
  Exec.runtimeMissingAbstractCannotCreateExclusion

screeningRuntimeCannotAdmit :
  Exec.RuntimeScreeningCreatesAuditAdmission → ⊥
screeningRuntimeCannotAdmit =
  Exec.runtimeScreeningCannotCreateAuditAdmission

slrHandoffRuntimeCannotAdmit :
  Exec.RuntimeSLRHandoffCreatesAuditAdmission → ⊥
slrHandoffRuntimeCannotAdmit =
  Exec.runtimeSLRHandoffCannotCreateAuditAdmission
