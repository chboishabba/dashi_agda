module DASHI.ComputerScience.RSA260RHBidiLeanBypassParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiActionConsumerSufficiencyExact as RSAAgda
import DASHI.ComputerScience.RSA260BidiLeanConsumerKernelBypassExact as RSALean
import DASHI.Analysis.RiemannUniversalEvenConeTransportGateExact as RHAgda
import DASHI.Analysis.RiemannUniversalEvenConeLeanSourceCustodyExact as RHLean

------------------------------------------------------------------------
-- RSA / RH LEAN-BYPASS PARETO SELECTOR
--
-- This is the Monster-style route selector for the bidi programme.
--
-- RSA:
--   existing Agda/runtime action-kernel receipts
--       versus
--   a generic Lean theorem saying observational equality is exactly difference
--   in the intersection of consumer kernels, with joint injectivity when that
--   intersection is bottom.
--
-- RH:
--   existing Agda/Python one-sided ascent
--       versus
--   (a) locating the historical cited Lean owner, or
--   (b) reproving only the minimal nonnegative universal-even-cone producer.
--
-- The routes are intentionally Pareto-incomparable until execution.  Failure
-- of a Lean probe does not invalidate the existing route; success does not
-- manufacture same-object/domain bindings.
------------------------------------------------------------------------

rsaAgdaBoundary : RSAAgda.RSAActionConsumerSufficiencyBoundary
rsaAgdaBoundary = RSAAgda.canonicalRSAActionConsumerSufficiencyBoundary

rsaLeanBoundary : RSALean.LeanConsumerKernelBypassBoundary
rsaLeanBoundary = RSALean.canonicalLeanConsumerKernelBypassBoundary

rhAgdaBoundary : RHAgda.UniversalEvenConeTransportBoundary
rhAgdaBoundary = RHAgda.canonicalUniversalEvenConeTransportBoundary

rhLeanBoundary : RHLean.UniversalEvenConeLeanSourceCustodyBoundary
rhLeanBoundary = RHLean.canonicalUniversalEvenConeLeanSourceCustodyBoundary

data RSARoute : Set where
  agdaRuntimeActionKernelRoute : RSARoute
  leanGenericJointKernelRoute : RSARoute

data RHRoute : Set where
  existingAgdaPythonAscentRoute : RHRoute
  locateHistoricalLeanOwnerRoute : RHRoute
  minimalCurrentLeanProducerRoute : RHRoute

preferredRSAProbe : RSARoute
preferredRSAProbe = leanGenericJointKernelRoute

preferredRHProbe : RHRoute
preferredRHProbe = minimalCurrentLeanProducerRoute

------------------------------------------------------------------------
-- WrongType / route-authority firewalls.
------------------------------------------------------------------------

data LeanGenericTheoremCreatesRSASameObjectBinding : Set where
data MinimalRHTaperProducerCreatesStrictRHMargin : Set where
data FailedLeanProbeInvalidatesExistingRoute : Set where

genericLeanDoesNotCreateRSABinding :
  LeanGenericTheoremCreatesRSASameObjectBinding -> ⊥
genericLeanDoesNotCreateRSABinding ()

minimalRHTaperDoesNotCreateStrictMargin :
  MinimalRHTaperProducerCreatesStrictRHMargin -> ⊥
minimalRHTaperDoesNotCreateStrictMargin ()

failedLeanProbeDoesNotInvalidateRoute :
  FailedLeanProbeInvalidatesExistingRoute -> ⊥
failedLeanProbeDoesNotInvalidateRoute ()

record RSA260RHBidiLeanBypassParetoBoundary : Set where
  constructor rsa260-rh-bidi-lean-bypass-pareto-boundary
  field
    existingAgdaRoutesRetained : Bool
    routesParetoIncomparableBeforeExecution : Bool

    rsaLeanGenericKernelRouteHighestAlphaProbe : Bool
    rsaLeanSourceWritten : Bool
    rsaLeanKernelReceiptObserved : Bool
    rsaLeanCrossProverTransportObserved : Bool
    rsaLeanSameObjectCADOBindingPaid : Bool

    rhHistoricalLeanOwnerLocated : Bool
    rhHistoricalLeanKernelReceiptObserved : Bool
    rhMinimalLeanProducerRouteHighestAlphaProbe : Bool
    rhMinimalLeanProducerSourceWritten : Bool
    rhMinimalLeanProducerKernelReceiptObserved : Bool
    rhMinimalProducerTransportedToFinalCarrier : Bool

    failedLeanProbeInvalidatesExistingRoute : Bool
    oeisCanSelectEitherRouteByProofAuthority : Bool

    rsaFallback : String
    rhFallback : String
open RSA260RHBidiLeanBypassParetoBoundary public

canonicalRSA260RHBidiLeanBypassParetoBoundary :
  RSA260RHBidiLeanBypassParetoBoundary
canonicalRSA260RHBidiLeanBypassParetoBoundary =
  rsa260-rh-bidi-lean-bypass-pareto-boundary
    true
    true
    true
    true
    false
    false
    false
    false
    false
    true
    false
    false
    false
    false
    false
    "retain the existing Agda/runtime action-consumer route: complete the chunked broader action portfolio, localize any consumer collision, and keep exact coefficient replay as the sufficient upper endpoint"
    "retain the existing Agda/Python semantic-ascent route: same-object final taper transport, phase weld, positive-part pointwise majorant, certified cell upper, finite fold, and strict near/complement margin"
