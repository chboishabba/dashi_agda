module DASHI.Crypto.ShorCertifiedFourierSamplingRegression where

open import DASHI.Core.Prelude

import DASHI.Algebra.Quantum.FiniteQuantumRegister as Finite
import DASHI.Algebra.Quantum.GeneralShor as Shor
import DASHI.Algebra.Quantum.ShorCyclicQFTCarrierTransportExact as Fourier
import DASHI.Algebra.Quantum.ShorAmplitudeExecutionPrefixExact as Prefix
import DASHI.Crypto.ShorOrderFinding as Order
import DASHI.Crypto.ShorReversiblePowModOracleWeldExact as PowModWeld
import DASHI.Crypto.ShorCertifiedFourierSamplingExact as Sampling

------------------------------------------------------------------------
-- RED regression: successful sampling must mean that the observed candidate
-- carries an exact-order certificate; the compiled machine then recovers r.
------------------------------------------------------------------------

certifiedSamplingMachineExists :
  ∀ {N a r} →
  (P : Order.ModularOrderProblem N a r) →
  {B : Finite.FiniteBasis} →
  {R : Finite.FiniteQuantumRegister B} →
  {SourceState : Set} →
  {sourceDFT : Fourier.CyclicDFTAction SourceState} →
  (prefix : Prefix.ShorAmplitudeExecutionPrefix
    B a N (PowModWeld.orderModulusNonZero P) R sourceDFT) →
  Sampling.ShoreFourierObservationSemantics P prefix →
  Shor.ShorPeriodFindingMachine (Order.asHiddenPeriodProblem P)
certifiedSamplingMachineExists = Sampling.compileCertifiedFourierSamplingMachine

successfulCandidateRecoversExactOrder :
  ∀ {N a r} →
  (P : Order.ModularOrderProblem N a r) →
  {B : Finite.FiniteBasis} →
  {R : Finite.FiniteQuantumRegister B} →
  {SourceState : Set} →
  {sourceDFT : Fourier.CyclicDFTAction SourceState} →
  (prefix : Prefix.ShorAmplitudeExecutionPrefix
    B a N (PowModWeld.orderModulusNonZero P) R sourceDFT) →
  (S : Sampling.ShoreFourierObservationSemantics P prefix) →
  (seed : Nat) →
  Shor.periodSuccessful
    (Sampling.compileCertifiedFourierSamplingMachine P prefix S)
    (Shor.periodExecute
      (Sampling.compileCertifiedFourierSamplingMachine P prefix S)
      seed) →
  Shor.recoverPeriod
    (Sampling.compileCertifiedFourierSamplingMachine P prefix S)
    (Shor.periodExecute
      (Sampling.compileCertifiedFourierSamplingMachine P prefix S)
      seed)
  ≡ r
successfulCandidateRecoversExactOrder P prefix S seed success =
  Shor.periodSuccessfulRecovery
    (Sampling.compileCertifiedFourierSamplingMachine P prefix S)
    seed
    success
