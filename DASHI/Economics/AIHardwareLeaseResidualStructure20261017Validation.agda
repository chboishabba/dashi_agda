module DASHI.Economics.AIHardwareLeaseResidualStructure20261017Validation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Economics.AIHardwareLeaseResidualStructure20261017Exact as Lease

fmvCappedOptionPaid : Lease.fmvOrPercentOption Lease.iren36MonthLease ≡ true
fmvCappedOptionPaid = Lease.fmvCappedOptionPaid

oneDollarOptionPaid : Lease.oneDollarBuyout Lease.iren24MonthLease ≡ true
oneDollarOptionPaid = Lease.oneDollarOptionPaid

optionNotMarketResidual : Lease.optionPriceEqualsMarketResidual Lease.currentLeaseResidualBoundary ≡ false
optionNotMarketResidual = Lease.optionDoesNotEqualMarketResidual
