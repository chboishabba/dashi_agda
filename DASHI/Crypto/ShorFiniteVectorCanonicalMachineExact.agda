module DASHI.Crypto.ShorFiniteVectorCanonicalMachineExact where

open import DASHI.Core.Prelude

import DASHI.Foundations.Base369Nat as B369
import DASHI.Algebra.Quantum.GeneralShor as Shor
import DASHI.Algebra.Quantum.ShorCyclicPhaseAmplitudeQFTExact as Phase
import DASHI.Algebra.Quantum.ShorFiniteVectorAmplitudeRegisterExact as Vector
import DASHI.Algebra.Quantum.ShorFiniteVectorExecutionPrefixExact as VectorPrefix
import DASHI.Crypto.ShorOrderFinding as Order
import DASHI.Crypto.ShorReversiblePowModOracleWeldExact as PowModWeld
import DASHI.Crypto.ShorFiniteVectorSupportedObservationExact as Supported
import DASHI.Crypto.ShorCanonicalCoefficientSupportExact as CanonicalSupport
import DASHI.Crypto.ShorFiniteVectorContinuedFractionMachineExact as Continued

------------------------------------------------------------------------
-- CANONICAL PREFERRED LOGICAL SHOR MACHINE
--
-- This is the narrowest preferred compiler currently available in the repo.
-- It fixes both previously-free classical semantics:
--
--   coefficient support = coefficient != zero
--   candidate extractor  = concrete continued-fraction / period-equation scan
--
-- and therefore takes only:
--
--   * the literal cyclic-QFT inversion authority, and
--   * a selector returning a genuinely supported exponent from the exact
--     post-QFT finite-vector state.
--
-- That selector is intentionally NOT manufactured here.  Turning amplitudes
-- into a stochastic/Born outcome law belongs to the probability layer.
------------------------------------------------------------------------

compileFiniteVectorCanonicalMachine :
  ∀ {N a r Q Coefficient}
    (P : Order.ModularOrderProblem N a r)
    (qNonZero : B369.NonZero Q)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q)
    (I : Vector.VectorCyclicPhaseInversionAuthority A)
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
      Supported.SupportedExponentOutcome
        (CanonicalSupport.canonicalCoefficientSupport A)
        state) →
  Shor.ShorPeriodFindingMachine (Order.asHiddenPeriodProblem P)
compileFiniteVectorCanonicalMachine
  P qNonZero A I seed selectOutcome =
  Continued.compileFiniteVectorContinuedFractionMachine
    P qNonZero A I
    (CanonicalSupport.canonicalCoefficientSupport A)
    seed
    selectOutcome

record ShorFiniteVectorCanonicalMachineBoundary : Set where
  constructor shorFiniteVectorCanonicalMachineBoundary
  field
    exactPowModOracleUsed : Bool
    canonicalFiniteAmplitudeCarrierUsed : Bool
    literalCyclicCharacterQFTUsed : Bool
    canonicalNotZeroSupportUsed : Bool
    concreteContinuedFractionCandidateUsed : Bool
    exactOrderVerifierUsed : Bool
    freeSupportPredicateRemaining : Bool
    freeCandidateExtractorRemaining : Bool
    cyclicCharacterResolutionStillRequired : Bool
    stochasticOutcomeSelectionStillRequired : Bool
    probabilityLowerBoundStillRequired : Bool

canonicalShorFiniteVectorCanonicalMachineBoundary :
  ShorFiniteVectorCanonicalMachineBoundary
canonicalShorFiniteVectorCanonicalMachineBoundary =
  shorFiniteVectorCanonicalMachineBoundary
    true true true true true true false false true true true
