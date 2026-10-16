module DASHI.Economics.AIAustraliaDataCentrePolicyShift20261016Validation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Economics.AIAustraliaDataCentrePolicyShift20261016Exact as Policy

modelGuardrailsCurrentlyProceedingFalse :
  Policy.generalMandatoryModelGuardrailsProceeding Policy.currentPolicyShift ≡ false
modelGuardrailsCurrentlyProceedingFalse = refl

dataCentreExpectationsCurrentTrue :
  Policy.currentDataCentreExpectations Policy.currentPolicyShift ≡ true
dataCentreExpectationsCurrentTrue = refl

announcedMandatoryInfrastructureRulesTrue :
  Policy.announcedFutureMandatoryDataCentreStandards Policy.currentPolicyShift ≡ true
announcedMandatoryInfrastructureRulesTrue = refl

enactedLegalDutyStillOpen :
  Policy.newMandatoryDataCentreDutyEnacted Policy.currentPolicyShift ≡ false
enactedLegalDutyStillOpen = refl

modelMoatNotPaid :
  Policy.modelComplianceMoatEstablished Policy.currentPolicyShift ≡ false
modelMoatNotPaid = refl
