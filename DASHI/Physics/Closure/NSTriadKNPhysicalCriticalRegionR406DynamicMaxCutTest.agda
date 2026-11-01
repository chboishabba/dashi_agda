module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406DynamicMaxCutTest where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406DynamicMaxCutExact as Cut

dynamicAlgebraClosed : Cut.b7R406DebtPlusFluxTangentDecompositionClosed ≡ true
dynamicAlgebraClosed = refl

actualDerivativeStillOpen : Cut.b7ActualFluxDerivativeClosed ≡ false
actualDerivativeStillOpen = refl

quarticDebtPaymentStillOpen : Cut.b7QuarticGramDebtPaymentClosed ≡ false
quarticDebtPaymentStillOpen = refl
