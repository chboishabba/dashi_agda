module DASHI.Economics.AICapitalMaxCut20261017Validation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Economics.AICapitalMaxCut20261017Exact as MaxCut

financingCohortPaid : MaxCut.financingCohortStructurePaid MaxCut.currentMaxCut ≡ true
financingCohortPaid = MaxCut.financingCohortPaid

companyOutcomesPaid : MaxCut.companyOutcomeCoordinatesPaid MaxCut.currentMaxCut ≡ true
companyOutcomesPaid = MaxCut.companyOutcomeCoordinatesPaidProof

providerDirectCostPaid : MaxCut.providerDirectCostCoordinatePaid MaxCut.currentMaxCut ≡ true
providerDirectCostPaid = MaxCut.providerDirectCostPaid

namedCashStillOpen : MaxCut.namedPayerCashPaid MaxCut.currentMaxCut ≡ false
namedCashStillOpen = MaxCut.namedCashStillOpen

marginalCostStillOpen : MaxCut.pureInferenceMarginalCostPaid MaxCut.currentMaxCut ≡ false
marginalCostStillOpen = MaxCut.marginalCostStillOpen

terminalRegimeStillOpen : MaxCut.terminalRegimeSelected MaxCut.currentMaxCut ≡ false
terminalRegimeStillOpen = MaxCut.terminalRegimeStillOpen
