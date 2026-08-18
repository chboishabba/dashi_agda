module DASHI.Ontology.ProgenitorParentConsultationDecisionSensitivityExact where

open import DASHI.Core.Prelude using (Bool; true; false; _≡_; refl)

import DASHI.Reasoning.RelationalChronologyProjectionBoundary as Chronology
import DASHI.Reasoning.RelationalSharedStateUpdate as Shared
import DASHI.Governance.DiachronicDelegatedAuthorityBoundary as Diachronic
open import DASHI.Ontology.ProgenitorParentHyperfabric using (_×_; _,_)

------------------------------------------------------------------------
-- Hearing is not uptake, decision sensitivity, agreement, or authority.
--
-- This imports the existing role-general pseudo-consultation witness rather
-- than constructing another parent-specific consultation semantics.
------------------------------------------------------------------------

inputWasRequested :
  Shared.inputWasRequested Chronology.canonicalPseudoConsultation ≡ true
inputWasRequested = refl

inputWasNotDecisionSensitive :
  Shared.inputWasNotDecisionSensitive Chronology.canonicalPseudoConsultation ≡ true
inputWasNotDecisionSensitive = refl

unilateralDecisionWasLaterPresentedAsJoint :
  Shared.unilateralDecisionLaterPresentedAsJoint
    Chronology.canonicalPseudoConsultation ≡ true
unilateralDecisionWasLaterPresentedAsJoint = refl

requestedInputDoesNotEqualUptake :
  Chronology.requestedInputEqualsUptakePromotion
    Chronology.canonicalRelationalChronologyProjectionBoundary ≡ false
requestedInputDoesNotEqualUptake = refl

presentPreferenceDoesNotEqualJointAgreement :
  Chronology.presentPreferenceEqualsJointAgreementPromotion
    Chronology.canonicalRelationalChronologyProjectionBoundary ≡ false
presentPreferenceDoesNotEqualJointAgreement = refl

supporterCannotConvertConsultationIntoOverride :
  Diachronic.supporterCannotSelfAuthoriseOverride
    Diachronic.canonicalSupportedDecisionConditions ≡ true
supporterCannotConvertConsultationIntoOverride = refl

hearingDoesNotEstablishDecisionSensitivity :
  Shared.inputWasRequested Chronology.canonicalPseudoConsultation ≡ true
  × Shared.inputWasNotDecisionSensitive Chronology.canonicalPseudoConsultation ≡ true
hearingDoesNotEstablishDecisionSensitivity = refl , refl

record ParentConsultationDecisionBoundary : Set where
  constructor parentConsultationDecisionBoundary
  field
    inputRequested : Bool
    inputRequestedIsTrue : inputRequested ≡ true
    inputActuallyDecisionSensitive : Bool
    inputActuallyDecisionSensitiveIsFalse :
      inputActuallyDecisionSensitive ≡ false
    hearingPromotesToUptake : Bool
    hearingPromotesToUptakeIsFalse : hearingPromotesToUptake ≡ false
    presentPreferencePromotesToJointAgreement : Bool
    presentPreferencePromotesToJointAgreementIsFalse :
      presentPreferencePromotesToJointAgreement ≡ false
    supporterMaySelfAuthoriseOverride : Bool
    supporterMaySelfAuthoriseOverrideIsFalse :
      supporterMaySelfAuthoriseOverride ≡ false

canonicalParentConsultationDecisionBoundary : ParentConsultationDecisionBoundary
canonicalParentConsultationDecisionBoundary =
  parentConsultationDecisionBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
