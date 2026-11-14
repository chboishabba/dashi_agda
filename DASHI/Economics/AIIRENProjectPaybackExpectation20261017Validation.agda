module DASHI.Economics.AIIRENProjectPaybackExpectation20261017Validation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Economics.AIIRENProjectPaybackExpectation20261017Exact as Expectation

forecastPaid : Expectation.companyPaybackExpectationPaid Expectation.irenSelectedProjectExpectation ≡ true
forecastPaid = Expectation.forecastPaid

realisationOpen : Expectation.realisedPaybackPaid Expectation.irenSelectedProjectExpectation ≡ false
realisationOpen = Expectation.realisedPaybackStillOpen
