module DASHI.Algebra.Quantum.ShorPeriodExecutionPipelineRegression where

open import DASHI.Core.Prelude

import DASHI.Algebra.Quantum.FiniteQuantumRegister as Finite
import DASHI.Algebra.Quantum.GeneralShor as Shor
import DASHI.Algebra.Quantum.ShorCyclicQFTCarrierTransportExact as Fourier
import DASHI.Algebra.Quantum.ShorAmplitudeExecutionPrefixExact as Prefix
import DASHI.Algebra.Quantum.ShorPeriodExecutionPipelineExact as Pipeline

------------------------------------------------------------------------
-- RED regression: periodExecute must be compiled from the same-register
-- oracle/QFT prefix plus explicit sampling semantics, not supplied independently.
------------------------------------------------------------------------

machineFromPipeline :
  ∀ {B : Finite.FiniteBasis}
    {base modulus : Nat}
    {modulusNonZero}
    {R : Finite.FiniteQuantumRegister B}
    {SourceState : Set}
    {sourceDFT : Fourier.CyclicDFTAction SourceState}
    {H : Shor.HiddenPeriodProblem} →
  (prefix : Prefix.ShorAmplitudeExecutionPrefix
    B base modulus modulusNonZero R sourceDFT) →
  Pipeline.ShorSamplingPipeline H prefix →
  Shor.ShorPeriodFindingMachine H
machineFromPipeline = Pipeline.compileShorPeriodFindingMachine

executeIsOracleThenQFTThenObservation :
  ∀ {B : Finite.FiniteBasis}
    {base modulus : Nat}
    {modulusNonZero}
    {R : Finite.FiniteQuantumRegister B}
    {SourceState : Set}
    {sourceDFT : Fourier.CyclicDFTAction SourceState}
    {H : Shor.HiddenPeriodProblem} →
  (prefix : Prefix.ShorAmplitudeExecutionPrefix
    B base modulus modulusNonZero R sourceDFT) →
  (sampling : Pipeline.ShorSamplingPipeline H prefix) →
  (seed : Nat) →
  Shor.periodExecute
    (Pipeline.compileShorPeriodFindingMachine prefix sampling)
    seed
  ≡ Pipeline.observeFourierState sampling
      (Pipeline.fourierAfterOracle prefix sampling seed)
executeIsOracleThenQFTThenObservation prefix sampling seed = refl
