module DASHI.Economics.AIFinancingCustomerCreditPriceDifferential20261017Validation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Economics.AIFinancingCustomerCreditPriceDifferential20261017Exact as Price

selectedDifferentialPaid : Price.selectedRateDifferenceBasisPoints Price.irenSelectedFinancingDifferential ≡ 300
selectedDifferentialPaid = Price.selectedDifferentialIs300bp

customerCreditCausalEffectOpen : Price.pureCustomerCreditCausalEffectPaid Price.irenSelectedFinancingDifferential ≡ false
customerCreditCausalEffectOpen = Price.causalEffectStillOpen

sameCompanyObservationPaid : Price.sameCompanyObservation Price.irenSelectedFinancingDifferential ≡ true
sameCompanyObservationPaid = Price.sameCompanyObservationPaid
