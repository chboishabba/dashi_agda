module DASHI.Economics.AIFinancingCohortCompanyOutcomeCoordinates20261017Validation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Economics.AIFinancingCohortCompanyOutcomeCoordinates20261017Exact as Outcome

nebiusAdvanceDrivenCashPaid : Outcome.customerAdvanceMaterialToOCF Outcome.nebiusH12026 ≡ true
nebiusAdvanceDrivenCashPaid = Outcome.nebiusAdvanceDrivenCashPaid

nebiusOperatingLossPaid : Outcome.operatingLossObserved Outcome.nebiusH12026 ≡ true
nebiusOperatingLossPaid = Outcome.nebiusOperatingLossPaid

irenOperatingLossPaid : Outcome.operatingLossObserved Outcome.irenFY2026 ≡ true
irenOperatingLossPaid = Outcome.irenOperatingLossPaid

positiveOCFNotProjectReturn : Outcome.positiveOCFSelectsProjectReturn Outcome.currentCompanyOutcomeBoundary ≡ false
positiveOCFNotProjectReturn = Outcome.positiveOCFDoesNotSelectProjectReturn

companyOutcomeNotProjectOutcome : Outcome.companyOutcomeSelectsProjectOutcome Outcome.currentCompanyOutcomeBoundary ≡ false
companyOutcomeNotProjectOutcome = Outcome.companyOutcomeDoesNotSelectProjectOutcome
