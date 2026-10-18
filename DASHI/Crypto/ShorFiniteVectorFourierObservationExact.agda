module DASHI.Crypto.ShorFiniteVectorFourierObservationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Fin.Base using (Fin; toℕ)

import DASHI.Foundations.Base369Nat as B369
import DASHI.Algebra.Quantum.QuantumFourierTransformFinite as QFT
import DASHI.Algebra.Quantum.ShorCyclicPhaseAmplitudeQFTExact as Phase
import DASHI.Algebra.Quantum.ShorFiniteVectorAmplitudeRegisterExact as Vector
import DASHI.Algebra.Quantum.ShorFiniteVectorExecutionPrefixExact as VectorPrefix
import DASHI.Crypto.ShorOrderFinding as Order
import DASHI.Crypto.ShorCertifiedFourierSamplingExact as Certified
import DASHI.Crypto.ShorReversiblePowModOracleWeldExact as PowModWeld

------------------------------------------------------------------------
-- FINITE-VECTOR FOURIER OBSERVATION ABI
--
-- The preferred vector route has a literal exponent carrier Fin Q.  Therefore,
-- once an exponent outcome k : Fin Q has been selected from the post-QFT state,
-- its raw Fourier sample is not another free object:
--
--     numerator   = toℕ k
--     denominator = Q.
--
-- This owner pays exactly that same-object seam and compiles the result into the
-- existing `ShorFourierObservationSemantics`.
--
-- It deliberately does NOT choose which k is observed.  Outcome selection is
-- an explicit state -> Fin Q input, so no Born distribution, randomness source,
-- nonzero-amplitude theorem, or success probability is manufactured here.
-- Likewise, candidate extraction remains an explicit FourierSample -> Nat
-- function with its source/reference retained by the existing observation type.
------------------------------------------------------------------------

canonicalFourierSample :
  (Q : Nat) →
  Fin Q →
  QFT.FourierSample
canonicalFourierSample Q outcome =
  QFT.mkFourierSample (toℕ outcome) Q

record FiniteVectorFourierObservationABI
    {N a r Q : Nat}
    {Coefficient : Set}
    (P : Order.ModularOrderProblem N a r)
    (qNonZero : B369.NonZero Q)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) : Set₁ where
  constructor finiteVectorFourierObservationABI
  field
    seedState :
      Nat →
      VectorPrefix.VectorRegisterState
        qNonZero
        (PowModWeld.orderModulusNonZero P)
        a A

    selectObservedExponent :
      VectorPrefix.VectorRegisterState
        qNonZero
        (PowModWeld.orderModulusNonZero P)
        a A →
      Fin Q

    candidateExtractor :
      QFT.FourierSample → Nat

    extractorReference :
      String

open FiniteVectorFourierObservationABI public

observeVectorFourierState :
  ∀ {N a r Q Coefficient}
    {P : Order.ModularOrderProblem N a r}
    {qNonZero : B369.NonZero Q}
    {A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q} →
  FiniteVectorFourierObservationABI P qNonZero A →
  VectorPrefix.VectorRegisterState
    qNonZero
    (PowModWeld.orderModulusNonZero P)
    a A →
  Certified.FourierOrderObservation P
observeVectorFourierState {Q = Q} abi state =
  let sample = canonicalFourierSample Q (selectObservedExponent abi state)
  in Certified.fourierOrderObservation
      sample
      (candidateExtractor abi sample)
      (extractorReference abi)

vectorFourierObservationSemantics :
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
      VectorPrefix.VectorRegisterState
        qNonZero
        (PowModWeld.orderModulusNonZero P)
        a A →
      Fin Q)
    (extractCandidate : QFT.FourierSample → Nat)
    (extractorRef : String) →
  Certified.ShorFourierObservationSemantics
    P
    (VectorPrefix.compileFiniteVectorExecutionPrefix
      qNonZero
      (PowModWeld.orderModulusNonZero P)
      a A I)
vectorFourierObservationSemantics P qNonZero A I
  seed selectOutcome extractCandidate extractorRef =
  Certified.shorFourierObservationSemantics
    seed
    (observeVectorFourierState abi)
  where
    abi : FiniteVectorFourierObservationABI P qNonZero A
    abi = finiteVectorFourierObservationABI
      seed
      selectOutcome
      extractCandidate
      extractorRef

observedRawSampleIsCanonicalOutcome :
  ∀ {N a r Q Coefficient}
    {P : Order.ModularOrderProblem N a r}
    {qNonZero : B369.NonZero Q}
    {A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q} →
  (abi : FiniteVectorFourierObservationABI P qNonZero A) →
  (state :
    VectorPrefix.VectorRegisterState
      qNonZero
      (PowModWeld.orderModulusNonZero P)
      a A) →
  Certified.rawFourierSample (observeVectorFourierState abi state)
  ≡ canonicalFourierSample Q (selectObservedExponent abi state)
observedRawSampleIsCanonicalOutcome abi state = refl

observedCandidateComesFromCanonicalSample :
  ∀ {N a r Q Coefficient}
    {P : Order.ModularOrderProblem N a r}
    {qNonZero : B369.NonZero Q}
    {A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q} →
  (abi : FiniteVectorFourierObservationABI P qNonZero A) →
  (state :
    VectorPrefix.VectorRegisterState
      qNonZero
      (PowModWeld.orderModulusNonZero P)
      a A) →
  Certified.observedCandidate (observeVectorFourierState abi state)
  ≡ candidateExtractor abi
      (canonicalFourierSample Q (selectObservedExponent abi state))
observedCandidateComesFromCanonicalSample abi state = refl

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

record ShorFiniteVectorFourierObservationBoundary : Set where
  constructor shorFiniteVectorFourierObservationBoundary
  field
    exponentOutcomeCarrierIsFinQ : Bool
    rawSampleNumeratorIsObservedExponent : Bool
    rawSampleDenominatorIsQ : Bool
    candidateConsumesThatExactRawSample : Bool
    extractorReferenceRetained : Bool
    outcomeSelectionConstructedHere : Bool
    stochasticMeasurementConstructedHere : Bool
    samplingDistributionConstructedHere : Bool
    continuedFractionCorrectnessConstructedHere : Bool
    successProbabilityConstructedHere : Bool

canonicalShorFiniteVectorFourierObservationBoundary :
  ShorFiniteVectorFourierObservationBoundary
canonicalShorFiniteVectorFourierObservationBoundary =
  shorFiniteVectorFourierObservationBoundary
    true true true true true false false false false false
