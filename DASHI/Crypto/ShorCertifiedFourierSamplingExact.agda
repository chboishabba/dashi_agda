module DASHI.Crypto.ShorCertifiedFourierSamplingExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Algebra.Quantum.FiniteQuantumRegister as Finite
import DASHI.Algebra.Quantum.QuantumFourierTransformFinite as QFT
import DASHI.Algebra.Quantum.GeneralShor as Shor
import DASHI.Algebra.Quantum.ShorCyclicQFTCarrierTransportExact as Fourier
import DASHI.Algebra.Quantum.ShorAmplitudeExecutionPrefixExact as Prefix
import DASHI.Algebra.Quantum.ShorPeriodExecutionPipelineExact as Pipeline
import DASHI.Crypto.FiniteFactorArithmetic as Factor
import DASHI.Crypto.ShorOrderFinding as Order
import DASHI.Crypto.ShorReversiblePowModOracleWeldExact as PowModWeld
import DASHI.Crypto.ShorFourierOrderCandidateVerificationExact as Verify

------------------------------------------------------------------------
-- Q3 CERTIFIED FOURIER SAMPLING
--
-- The raw observation/extractor may propose any candidate Nat.  It becomes a
-- *successful* Shor sample only when the candidate carries an
-- `ExactOrderCertificate N a candidate`.
--
-- Thus `ShorSuccessEvidence` is not a free success flag on this preferred
-- route: its `success` field is exactly arithmetic evidence that the observed
-- candidate is the true modular order.  Exact-order uniqueness then supplies
-- the recovery theorem required by `ShorPeriodFindingMachine`.
------------------------------------------------------------------------

record FourierOrderObservation
    {N a r : Nat}
    (P : Order.ModularOrderProblem N a r) : Set where
  constructor fourierOrderObservation
  field
    rawFourierSample : QFT.FourierSample
    observedCandidate : Nat
    extractorReference : String

open FourierOrderObservation public

CandidateExact :
  ∀ {N a r} →
  (P : Order.ModularOrderProblem N a r) →
  FourierOrderObservation P → Set
CandidateExact {N} {a} P observation =
  Factor.ExactOrderCertificate N a (observedCandidate observation)

record ShorFourierObservationSemantics
    {N a r : Nat}
    (P : Order.ModularOrderProblem N a r)
    {B : Finite.FiniteBasis}
    {R : Finite.FiniteQuantumRegister B}
    {SourceState : Set}
    {sourceDFT : Fourier.CyclicDFTAction SourceState}
    (prefix : Prefix.ShorAmplitudeExecutionPrefix
      B a N (PowModWeld.orderModulusNonZero P) R sourceDFT) : Set₁ where
  constructor shorFourierObservationSemantics
  field
    seedState : Nat → Finite.State R
    observeFourierState :
      Finite.State R → FourierOrderObservation P

open ShorFourierObservationSemantics public

certifiedFourierSamplingPipeline :
  ∀ {N a r} →
  (P : Order.ModularOrderProblem N a r) →
  {B : Finite.FiniteBasis} →
  {R : Finite.FiniteQuantumRegister B} →
  {SourceState : Set} →
  {sourceDFT : Fourier.CyclicDFTAction SourceState} →
  (prefix : Prefix.ShorAmplitudeExecutionPrefix
    B a N (PowModWeld.orderModulusNonZero P) R sourceDFT) →
  ShorFourierObservationSemantics P prefix →
  Pipeline.ShorSamplingPipeline
    (Order.asHiddenPeriodProblem P)
    prefix
certifiedFourierSamplingPipeline {r = r} {R = R} P prefix semantics =
  Pipeline.shorSamplingPipeline
    (FourierOrderObservation P)
    (seedState semantics)
    (observeFourierState semantics)
    (CandidateExact P)
    observedCandidate
    successfulRecovery
  where
    finalState : Nat → Finite.State R
    finalState seed =
      QFT.fourier
        (Prefix.amplitudeFourierTransform prefix)
        (Finite.run
          (Prefix.amplitudeOracleCircuit prefix)
          (seedState semantics seed))

    successfulRecovery :
      ∀ seed →
      CandidateExact P
        (observeFourierState semantics (finalState seed)) →
      observedCandidate
        (observeFourierState semantics (finalState seed))
      ≡ r
    successfulRecovery seed candidateCert =
      Verify.exactOrderCertificateUnique
        candidateCert
        (Order.exactOrder P)

compileCertifiedFourierSamplingMachine :
  ∀ {N a r} →
  (P : Order.ModularOrderProblem N a r) →
  {B : Finite.FiniteBasis} →
  {R : Finite.FiniteQuantumRegister B} →
  {SourceState : Set} →
  {sourceDFT : Fourier.CyclicDFTAction SourceState} →
  (prefix : Prefix.ShorAmplitudeExecutionPrefix
    B a N (PowModWeld.orderModulusNonZero P) R sourceDFT) →
  ShorFourierObservationSemantics P prefix →
  Shor.ShorPeriodFindingMachine (Order.asHiddenPeriodProblem P)
compileCertifiedFourierSamplingMachine P prefix semantics =
  Pipeline.compileShorPeriodFindingMachine
    prefix
    (certifiedFourierSamplingPipeline P prefix semantics)

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

record CertifiedFourierSamplingBoundary : Set where
  constructor certifiedFourierSamplingBoundary
  field
    periodExecuteComesFromOracleQFTPipeline : Bool
    observationFunctionExplicit : Bool
    extractorReferenceRetained : Bool
    successMeansExactOrderCertificate : Bool
    successfulRecoveryCompiledFromUniqueness : Bool
    continuedFractionCorrectnessProvedHere : Bool
    samplingDistributionProvedHere : Bool
    probabilityLowerBoundProvedHere : Bool

canonicalCertifiedFourierSamplingBoundary :
  CertifiedFourierSamplingBoundary
canonicalCertifiedFourierSamplingBoundary =
  certifiedFourierSamplingBoundary
    true true true true true false false false
