module DASHI.Crypto.ShorFiniteVectorCertifiedMachineExact where

open import DASHI.Core.Prelude

import DASHI.Foundations.Base369Nat as B369
import DASHI.Algebra.Quantum.GeneralShor as Shor
import DASHI.Algebra.Quantum.ShorCyclicPhaseAmplitudeQFTExact as Phase
import DASHI.Algebra.Quantum.ShorFiniteVectorAmplitudeRegisterExact as Vector
import DASHI.Algebra.Quantum.ShorFiniteVectorExecutionPrefixExact as VectorPrefix
import DASHI.Crypto.ShorOrderFinding as Order
import DASHI.Crypto.ShorCertifiedFourierSamplingExact as Certified
import DASHI.Crypto.ShorFiniteVectorSupportedObservationExact as Supported
import DASHI.Crypto.ShorReversiblePowModOracleWeldExact as PowModWeld

------------------------------------------------------------------------
-- PREFERRED FINITE-VECTOR CERTIFIED SHOR MACHINE JOIN
--
-- This module contains no new arithmetic theorem.  It simply joins the already
-- separated obligations on the preferred route:
--
--   exact RSA.powMod oracle on the canonical finite vector carrier
--   + literal cyclic character QFT inversion on that SAME carrier
--   + supported exponent observation
--   + existing exact-order verifier
--
-- into the repository's existing `ShorPeriodFindingMachine`.
--
-- The remaining non-compiler inputs stay visible:
--   * `VectorCyclicPhaseInversionAuthority` -- the normalized cyclic DFT math;
--   * `CoefficientSupportAuthority` and supported-outcome selector;
--   * candidate extraction from the exact raw Fourier sample.
--
-- No sampling probability, continued-fraction correctness or hardware claim is
-- introduced here.
------------------------------------------------------------------------

compileFiniteVectorCertifiedMachine :
  ∀ {N a r Q Coefficient}
    (P : Order.ModularOrderProblem N a r)
    (qNonZero : B369.NonZero Q)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q)
    (I : Vector.VectorCyclicPhaseInversionAuthority A)
    (support : Supported.CoefficientSupportAuthority A) →
  Supported.FiniteVectorSupportedObservationABI P qNonZero A support →
  Shor.ShorPeriodFindingMachine (Order.asHiddenPeriodProblem P)
compileFiniteVectorCertifiedMachine {a = a} P qNonZero A I support abi =
  Certified.compileCertifiedFourierSamplingMachine
    P
    prefix
    (Supported.supportedObservationSemantics
      P qNonZero A I support abi)
  where
    prefix =
      VectorPrefix.compileFiniteVectorExecutionPrefix
        qNonZero
        (PowModWeld.orderModulusNonZero P)
        a A I

record ShorFiniteVectorCertifiedMachineBoundary : Set where
  constructor shorFiniteVectorCertifiedMachineBoundary
  field
    preferredVectorCarrierUsed : Bool
    exactPowModOracleReused : Bool
    literalCyclicQFTReused : Bool
    supportedObservationReused : Bool
    exactOrderVerificationReused : Bool
    cyclicCharacterResolutionStillRequired : Bool
    observedOutcomeSelectionStillRequired : Bool
    candidateExtractorStillRequired : Bool
    samplingProbabilityStillRequired : Bool
    physicalRealizationStillRequired : Bool

canonicalShorFiniteVectorCertifiedMachineBoundary :
  ShorFiniteVectorCertifiedMachineBoundary
canonicalShorFiniteVectorCertifiedMachineBoundary =
  shorFiniteVectorCertifiedMachineBoundary
    true true true true true true true true true true
