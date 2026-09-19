module DASHI.Education.DigitalESDTitleAbstractScreeningRegression where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDTitleAbstractScreeningExact as Screen

screeningCannotCreateTruth :
  Screen.ScreeningDecisionCreatesSourceTruth → ⊥
screeningCannotCreateTruth =
  Screen.screeningDecisionDoesNotCreateSourceTruth

screeningCannotCreateAdmission :
  Screen.ScreeningDecisionCreatesSourceAuditAdmission → ⊥
screeningCannotCreateAdmission =
  Screen.screeningDecisionDoesNotCreateSourceAuditAdmission

metadataDuplicateCannotCreateStudyIdentity :
  Screen.MetadataDuplicateCreatesSameEmpiricalStudy → ⊥
metadataDuplicateCannotCreateStudyIdentity =
  Screen.metadataDuplicateDoesNotCreateSameEmpiricalStudy

excludedRecordsRemainLedgered :
  Screen.ExclusionMayBeDiscardedWithoutReceipt → ⊥
excludedRecordsRemainLedgered =
  Screen.exclusionMayNotBeDiscardedWithoutReceipt
