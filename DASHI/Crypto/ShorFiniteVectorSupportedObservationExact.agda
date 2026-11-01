module DASHI.Crypto.ShorFiniteVectorSupportedObservationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (suc)
open import Data.Fin.Base using (Fin)

import DASHI.Foundations.Base369Nat as B369
import DASHI.Algebra.Quantum.QuantumFourierTransformFinite as QFT
import DASHI.Algebra.Quantum.ShorCyclicPhaseAmplitudeQFTExact as Phase
import DASHI.Algebra.Quantum.ShorFiniteVectorAmplitudeRegisterExact as Vector
import DASHI.Algebra.Quantum.ShorFiniteVectorExecutionPrefixExact as VectorPrefix
import DASHI.Crypto.ShorOrderFinding as Order
import DASHI.Crypto.ShorReversiblePowModOracleWeldExact as PowModWeld
import DASHI.Crypto.ShorCertifiedFourierSamplingExact as Certified
import DASHI.Crypto.ShorFiniteVectorFourierObservationExact as RawObservation

------------------------------------------------------------------------
-- SUPPORTED FOURIER OUTCOME SEMANTICS
--
-- `ShorFiniteVectorFourierObservationExact` paid the exact object identity
--
--     k : Fin Q  ->  FourierSample (toℕ k) Q.
--
-- This owner tightens the remaining outcome-selection seam.  A selected
-- exponent is no longer an arbitrary Fin Q: it must carry a witness that at
-- least one target column at that exponent is classified nonzero in the actual
-- finite-vector state.
--
-- This is intentionally support semantics, not Born semantics.  We do not
-- assign weights, probabilities, randomness, frequencies, or a lower bound on
-- the chance of selecting any supported outcome.
------------------------------------------------------------------------

record CoefficientSupportAuthority
    {Q : Nat}
    {Coefficient : Set}
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) : Set₁ where
  constructor coefficientSupportAuthority
  field
    NonzeroCoefficient : Coefficient → Set
    zeroCoefficientNotNonzero :
      NonzeroCoefficient (Phase.zeroCoefficient A) → ⊥

open CoefficientSupportAuthority public

ExponentSupported :
  ∀ {Q N Coefficient}
    {A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q} →
  CoefficientSupportAuthority A →
  Vector.VectorAmplitudeState Q N A →
  Fin Q →
  Set
ExponentSupported {N = N} support state outcome =
  Σ (Fin (suc N)) λ target →
    NonzeroCoefficient support
      (Vector.tableLookup
        (Vector.amplitudeTable state)
        outcome target)

SupportedExponentOutcome :
  ∀ {Q N Coefficient}
    {A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q} →
  (support : CoefficientSupportAuthority A) →
  (state : Vector.VectorAmplitudeState Q N A) →
  Set
SupportedExponentOutcome {Q = Q} support state =
  Σ (Fin Q) λ outcome → ExponentSupported support state outcome

supportedFourierSample :
  ∀ {Q N Coefficient}
    {A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q}
    {support : CoefficientSupportAuthority A}
    {state : Vector.VectorAmplitudeState Q N A} →
  (Q : Nat) →
  SupportedExponentOutcome support state →
  QFT.FourierSample
supportedFourierSample Q selected =
  RawObservation.canonicalFourierSample Q (fst selected)

record FiniteVectorSupportedObservationABI
    {N a r Q : Nat}
    {Coefficient : Set}
    (P : Order.ModularOrderProblem N a r)
    (qNonZero : B369.NonZero Q)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q)
    (support : CoefficientSupportAuthority A) : Set₁ where
  constructor finiteVectorSupportedObservationABI
  field
    seedState :
      Nat →
      VectorPrefix.VectorRegisterState
        qNonZero
        (PowModWeld.orderModulusNonZero P)
        a A

    selectSupportedOutcome :
      (state :
        VectorPrefix.VectorRegisterState
          qNonZero
          (PowModWeld.orderModulusNonZero P)
          a A) →
      SupportedExponentOutcome support state

    candidateExtractor : QFT.FourierSample → Nat
    extractorReference : String

open FiniteVectorSupportedObservationABI public

supportedObservationSemantics :
  ∀ {N a r Q Coefficient}
    (P : Order.ModularOrderProblem N a r)
    (qNonZero : B369.NonZero Q)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q)
    (I : Vector.VectorCyclicPhaseInversionAuthority A)
    (support : CoefficientSupportAuthority A) →
  FiniteVectorSupportedObservationABI P qNonZero A support →
  Certified.ShorFourierObservationSemantics
    P
    (VectorPrefix.compileFiniteVectorExecutionPrefix
      qNonZero
      (PowModWeld.orderModulusNonZero P)
      a A I)
supportedObservationSemantics P qNonZero A I support abi =
  RawObservation.vectorFourierObservationSemantics
    P qNonZero A I
    (seedState abi)
    (λ state → fst (selectSupportedOutcome abi state))
    (candidateExtractor abi)
    (extractorReference abi)

selectedOutcomeSupportRetained :
  ∀ {N a r Q Coefficient}
    {P : Order.ModularOrderProblem N a r}
    {qNonZero : B369.NonZero Q}
    {A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q}
    {support : CoefficientSupportAuthority A} →
  (abi : FiniteVectorSupportedObservationABI P qNonZero A support) →
  (state :
    VectorPrefix.VectorRegisterState
      qNonZero
      (PowModWeld.orderModulusNonZero P)
      a A) →
  ExponentSupported support state
    (fst (selectSupportedOutcome abi state))
selectedOutcomeSupportRetained abi state =
  snd (selectSupportedOutcome abi state)

record ShorFiniteVectorSupportedObservationBoundary : Set where
  constructor shorFiniteVectorSupportedObservationBoundary
  field
    outcomeComesFromExactPostQFTCarrier : Bool
    selectedExponentCarriesSupportWitness : Bool
    zeroCoefficientExcludedFromSupport : Bool
    rawSampleStillCanonicalKOverQ : Bool
    stochasticSelectionConstructedHere : Bool
    bornWeightsConstructedHere : Bool
    normalizedProbabilityMeasureConstructedHere : Bool
    successProbabilityConstructedHere : Bool

canonicalShorFiniteVectorSupportedObservationBoundary :
  ShorFiniteVectorSupportedObservationBoundary
canonicalShorFiniteVectorSupportedObservationBoundary =
  shorFiniteVectorSupportedObservationBoundary
    true true true true false false false false
