module DASHI.Law.ClosedIsNotAdequateRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Law.ClosedIsNotAdequateExact as Closed
import DASHI.Law.ExactNonFactorabilityResidualCompilerExact as Residual

boundary : Closed.ClosedIsNotAdequateBoundary
boundary = Closed.canonicalClosedIsNotAdequateBoundary

noFreshIsNotAdequacy :
  Closed.noFreshDemandIsConsumerAdequacyProof boundary ≡ false
noFreshIsNotAdequacy =
  Closed.noFreshDemandIsConsumerAdequacyProofIsFalse boundary

formalWitnessCanCertify :
  Closed.kernelCheckedFactorsThroughMayCertifyAdequacy boundary ≡ true
formalWitnessCanCertify =
  Closed.kernelCheckedFactorsThroughMayCertifyAdequacyIsTrue boundary

nonfactorabilityReopensClosed :
  Closed.exactNonfactorabilityMayReopenClosedFrontier boundary ≡ true
nonfactorabilityReopensClosed =
  Closed.exactNonfactorabilityMayReopenClosedFrontierIsTrue boundary

temporalResidualIsExact :
  Residual.demandKind Closed.closedTimeErasureResidual ≡ Residual.resolveTemporal
temporalResidualIsExact =
  Closed.closedTimeErasureReopensTemporalResearch
