module DASHI.Crypto.ShorFiniteVectorContinuedFractionMachineExact where

open import DASHI.Core.Prelude

import DASHI.Foundations.Base369Nat as B369
import DASHI.Algebra.Quantum.GeneralShor as Shor
import DASHI.Algebra.Quantum.ShorCyclicPhaseAmplitudeQFTExact as Phase
import DASHI.Algebra.Quantum.ShorFiniteVectorAmplitudeRegisterExact as Vector
import DASHI.Algebra.Quantum.ShorFiniteVectorExecutionPrefixExact as VectorPrefix
import DASHI.Crypto.ShorOrderFinding as Order
import DASHI.Crypto.ShorReversiblePowModOracleWeldExact as PowModWeld
import DASHI.Crypto.ShorFiniteVectorSupportedObservationExact as Supported
import DASHI.Crypto.ShorFiniteVectorCertifiedMachineExact as CertifiedMachine
import DASHI.Crypto.ShorContinuedFractionCandidateExact as Candidate

------------------------------------------------------------------------
-- PREFERRED VECTOR SHOR MACHINE WITH CONCRETE CANDIDATE PRODUCER
--
-- This owner removes the last free `FourierSample -> Nat` function from the
-- preferred vector route.  The candidate extractor is definitionally the
-- concrete continued-fraction / modular-period producer in
-- `ShorContinuedFractionCandidateExact`.
--
-- Remaining explicit inputs are therefore:
--   * cyclic character-resolution / QFT inversion authority;
--   * coefficient support semantics;
--   * a supported post-QFT outcome selector.
--
-- Exact-order minimality and successful recovery are still provided only by the
-- existing exact-order verifier downstream.  No probability result is added.
------------------------------------------------------------------------

continuedFractionObservationABI :
  ∀ {N a r Q Coefficient}
    (P : Order.ModularOrderProblem N a r)
    (qNonZero : B369.NonZero Q)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q)
    (support : Supported.CoefficientSupportAuthority A)
    (seed : Nat →
      VectorPrefix.VectorRegisterState
        qNonZero
        (PowModWeld.orderModulusNonZero P)
        a A)
    (selectOutcome :
      (state :
        VectorPrefix.VectorRegisterState
          qNonZero
          (PowModWeld.orderModulusNonZero P)
          a A) →
      Supported.SupportedExponentOutcome support state) →
  Supported.FiniteVectorSupportedObservationABI P qNonZero A support
continuedFractionObservationABI P qNonZero A support seed selectOutcome =
  Supported.finiteVectorSupportedObservationABI
    seed
    selectOutcome
    (Candidate.continuedFractionPeriodCandidate P)
    "Shor 1997 SIAM J. Comput. 26(5), DOI 10.1137/S0097539795293172; DASHI concrete Euclidean/convergent producer"

compileFiniteVectorContinuedFractionMachine :
  ∀ {N a r Q Coefficient}
    (P : Order.ModularOrderProblem N a r)
    (qNonZero : B369.NonZero Q)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q)
    (I : Vector.VectorCyclicPhaseInversionAuthority A)
    (support : Supported.CoefficientSupportAuthority A)
    (seed : Nat →
      VectorPrefix.VectorRegisterState
        qNonZero
        (PowModWeld.orderModulusNonZero P)
        a A)
    (selectOutcome :
      (state :
        VectorPrefix.VectorRegisterState
          qNonZero
          (PowModWeld.orderModulusNonZero P)
          a A) →
      Supported.SupportedExponentOutcome support state) →
  Shor.ShorPeriodFindingMachine (Order.asHiddenPeriodProblem P)
compileFiniteVectorContinuedFractionMachine
  P qNonZero A I support seed selectOutcome =
  CertifiedMachine.compileFiniteVectorCertifiedMachine
    P qNonZero A I support
    (continuedFractionObservationABI
      P qNonZero A support seed selectOutcome)

record ShorFiniteVectorContinuedFractionMachineBoundary : Set where
  constructor shorFiniteVectorContinuedFractionMachineBoundary
  field
    canonicalVectorCarrierUsed : Bool
    exactPowModOracleUsed : Bool
    literalCyclicQFTUsed : Bool
    supportedOutcomeRequired : Bool
    concreteContinuedFractionProducerUsed : Bool
    freeCandidateExtractorRemoved : Bool
    exactOrderVerifierStillAuthoritative : Bool
    cyclicCharacterResolutionStillRequired : Bool
    stochasticOutcomeSelectionStillRequired : Bool
    successProbabilityStillRequired : Bool

canonicalShorFiniteVectorContinuedFractionMachineBoundary :
  ShorFiniteVectorContinuedFractionMachineBoundary
canonicalShorFiniteVectorContinuedFractionMachineBoundary =
  shorFiniteVectorContinuedFractionMachineBoundary
    true true true true true true true true true true
