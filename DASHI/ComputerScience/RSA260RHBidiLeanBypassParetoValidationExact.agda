module DASHI.ComputerScience.RSA260RHBidiLeanBypassParetoValidationExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.RSA260RHBidiLeanBypassParetoExact as P

boundary : P.RSA260RHBidiLeanBypassParetoBoundary
boundary = P.canonicalRSA260RHBidiLeanBypassParetoBoundary

_ : P.existingAgdaRoutesRetained boundary ≡ true
_ = refl

_ : P.rsaLeanGenericKernelRouteHighestAlphaProbe boundary ≡ true
_ = refl

_ : P.rhMinimalLeanProducerRouteHighestAlphaProbe boundary ≡ true
_ = refl

_ : P.routesParetoIncomparableBeforeExecution boundary ≡ true
_ = refl

_ : P.rsaLeanKernelReceiptObserved boundary ≡ false
_ = refl

_ : P.rhHistoricalLeanOwnerLocated boundary ≡ false
_ = refl

_ : P.rhMinimalLeanProducerSourceWritten boundary ≡ false
_ = refl

_ : P.failedLeanProbeInvalidatesExistingRoute boundary ≡ false
_ = refl
