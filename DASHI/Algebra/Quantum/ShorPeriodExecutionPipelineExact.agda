module DASHI.Algebra.Quantum.ShorPeriodExecutionPipelineExact where

open import DASHI.Core.Prelude
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Algebra.Quantum.FiniteQuantumRegister as Finite
import DASHI.Algebra.Quantum.QuantumFourierTransformFinite as QFT
import DASHI.Algebra.Quantum.GeneralShor as Shor
import DASHI.Algebra.Quantum.ShorCyclicQFTCarrierTransportExact as Fourier
import DASHI.Algebra.Quantum.ShorAmplitudeExecutionPrefixExact as Prefix

------------------------------------------------------------------------
-- Q2 PERIOD-EXECUTION COMPILER
--
-- `ShorPeriodFindingMachine.periodExecute` is intentionally broad.  This owner
-- supplies the preferred non-vacuous route: period execution is definitionally
-- the observation of a state produced by
--
--   seed preparation -> exact reversible oracle -> transported cyclic QFT.
--
-- Sampling/measurement and successful period recovery remain explicit inputs.
-- In particular, this file does not choose a sample equal to the known period,
-- and it does not derive a probability distribution from invertibility alone.
------------------------------------------------------------------------

record ShorSamplingPipeline
    {B : Finite.FiniteBasis}
    {base modulus : Nat}
    {modulusNonZero}
    {R : Finite.FiniteQuantumRegister B}
    {SourceState : Set}
    {sourceDFT : Fourier.CyclicDFTAction SourceState}
    (H : Shor.HiddenPeriodProblem)
    (prefix : Prefix.ShorAmplitudeExecutionPrefix
      B base modulus modulusNonZero R sourceDFT) : Set₁ where
  constructor shorSamplingPipeline
  field
    PeriodSample : Set

    seedState : Nat → Finite.State R

    observeFourierState :
      Finite.State R → PeriodSample

    sampleSuccessful : PeriodSample → Set

    recoverSamplePeriod : PeriodSample → Nat

    successfulPipelineRecovery :
      ∀ seed →
      sampleSuccessful
        (observeFourierState
          (QFT.fourier
            (Prefix.amplitudeFourierTransform prefix)
            (Finite.run
              (Prefix.amplitudeOracleCircuit prefix)
              (seedState seed)))) →
      recoverSamplePeriod
        (observeFourierState
          (QFT.fourier
            (Prefix.amplitudeFourierTransform prefix)
            (Finite.run
              (Prefix.amplitudeOracleCircuit prefix)
              (seedState seed))))
      ≡ Shor.period H

open ShorSamplingPipeline public

oracleAfterSeed :
  ∀ {B : Finite.FiniteBasis}
    {base modulus : Nat}
    {modulusNonZero}
    {R : Finite.FiniteQuantumRegister B}
    {SourceState : Set}
    {sourceDFT : Fourier.CyclicDFTAction SourceState}
    {H : Shor.HiddenPeriodProblem} →
  (prefix : Prefix.ShorAmplitudeExecutionPrefix
    B base modulus modulusNonZero R sourceDFT) →
  (sampling : ShorSamplingPipeline H prefix) →
  Nat → Finite.State R
oracleAfterSeed prefix sampling seed =
  Finite.run
    (Prefix.amplitudeOracleCircuit prefix)
    (seedState sampling seed)

fourierAfterOracle :
  ∀ {B : Finite.FiniteBasis}
    {base modulus : Nat}
    {modulusNonZero}
    {R : Finite.FiniteQuantumRegister B}
    {SourceState : Set}
    {sourceDFT : Fourier.CyclicDFTAction SourceState}
    {H : Shor.HiddenPeriodProblem} →
  (prefix : Prefix.ShorAmplitudeExecutionPrefix
    B base modulus modulusNonZero R sourceDFT) →
  (sampling : ShorSamplingPipeline H prefix) →
  Nat → Finite.State R
fourierAfterOracle prefix sampling seed =
  QFT.fourier
    (Prefix.amplitudeFourierTransform prefix)
    (oracleAfterSeed prefix sampling seed)

pipelineExecute :
  ∀ {B : Finite.FiniteBasis}
    {base modulus : Nat}
    {modulusNonZero}
    {R : Finite.FiniteQuantumRegister B}
    {SourceState : Set}
    {sourceDFT : Fourier.CyclicDFTAction SourceState}
    {H : Shor.HiddenPeriodProblem} →
  (prefix : Prefix.ShorAmplitudeExecutionPrefix
    B base modulus modulusNonZero R sourceDFT) →
  (sampling : ShorSamplingPipeline H prefix) →
  Nat → PeriodSample sampling
pipelineExecute prefix sampling seed =
  observeFourierState sampling
    (fourierAfterOracle prefix sampling seed)

compileShorPeriodFindingMachine :
  ∀ {B : Finite.FiniteBasis}
    {base modulus : Nat}
    {modulusNonZero}
    {R : Finite.FiniteQuantumRegister B}
    {SourceState : Set}
    {sourceDFT : Fourier.CyclicDFTAction SourceState}
    {H : Shor.HiddenPeriodProblem} →
  (prefix : Prefix.ShorAmplitudeExecutionPrefix
    B base modulus modulusNonZero R sourceDFT) →
  (sampling : ShorSamplingPipeline H prefix) →
  Shor.ShorPeriodFindingMachine H
compileShorPeriodFindingMachine {B} {R = R} prefix sampling = record
  { periodBasis = B
  ; periodRegister = R
  ; periodFourierTransform = Prefix.amplitudeFourierTransform prefix
  ; PeriodSample = PeriodSample sampling
  ; periodExecute = pipelineExecute prefix sampling
  ; periodSuccessful = sampleSuccessful sampling
  ; recoverPeriod = recoverSamplePeriod sampling
  ; periodSuccessfulRecovery = successfulPipelineRecovery sampling
  }

compiledPeriodExecuteIsPipeline :
  ∀ {B : Finite.FiniteBasis}
    {base modulus : Nat}
    {modulusNonZero}
    {R : Finite.FiniteQuantumRegister B}
    {SourceState : Set}
    {sourceDFT : Fourier.CyclicDFTAction SourceState}
    {H : Shor.HiddenPeriodProblem} →
  (prefix : Prefix.ShorAmplitudeExecutionPrefix
    B base modulus modulusNonZero R sourceDFT) →
  (sampling : ShorSamplingPipeline H prefix) →
  (seed : Nat) →
  Shor.periodExecute
    (compileShorPeriodFindingMachine prefix sampling)
    seed
  ≡ pipelineExecute prefix sampling seed
compiledPeriodExecuteIsPipeline prefix sampling seed = refl

------------------------------------------------------------------------
-- Frontier / authority boundary.
------------------------------------------------------------------------

record ShorPeriodExecutionPipelineBoundary : Set where
  constructor shorPeriodExecutionPipelineBoundary
  field
    periodExecuteFloatsFreeOfCircuit : Bool
    oracleAndQFTExecutionOrderFixed : Bool
    samplingObservationExplicit : Bool
    recoveryFunctionExplicit : Bool
    successfulRecoveryStillEvidence : Bool
    samplingDistributionProved : Bool
    successProbabilityProved : Bool

canonicalShorPeriodExecutionPipelineBoundary :
  ShorPeriodExecutionPipelineBoundary
canonicalShorPeriodExecutionPipelineBoundary =
  shorPeriodExecutionPipelineBoundary
    false true true true true false false
