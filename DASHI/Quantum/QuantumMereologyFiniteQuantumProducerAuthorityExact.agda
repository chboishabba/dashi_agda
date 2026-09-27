{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumMereologyFiniteQuantumProducerAuthorityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Quantum.QuantumMereologySourceAtlasExact as Sources

------------------------------------------------------------------------
-- CROSS-PROVER STATUS FOR THE FINITE QUANTUM PRODUCER
--
-- Lean source owners now provide:
-- * finite density matrices as PSD trace-one complex matrices,
-- * explicit finite bipartite partial trace,
-- * trace/Hermitian/PSD preservation under partial trace,
-- * unitary conjugation preserving density-matrix laws,
-- * finite pointer-projector trace readouts,
-- * linear and pointer entropy paths,
-- * derivative-backed t=0 entropy accelerations.
--
-- Agda records those as source-written/imported theorem authorities only until
-- exact-head Lean kernel evidence is available.
------------------------------------------------------------------------

record FiniteQuantumProducerAuthority : Set₁ where
  field
    DensityMatrixAuthority : Set
    densityMatrixAuthority : DensityMatrixAuthority

    PartialTraceAuthority : Set
    partialTraceAuthority : PartialTraceAuthority

    PartialTraceTracePreservationAuthority : Set
    partialTraceTracePreservationAuthority :
      PartialTraceTracePreservationAuthority

    PartialTraceHermitianPreservationAuthority : Set
    partialTraceHermitianPreservationAuthority :
      PartialTraceHermitianPreservationAuthority

    PartialTracePositivityAuthority : Set
    partialTracePositivityAuthority :
      PartialTracePositivityAuthority

    UnitaryDensityEvolutionAuthority : Set
    unitaryDensityEvolutionAuthority :
      UnitaryDensityEvolutionAuthority

    PointerProbabilityAuthority : Set
    pointerProbabilityAuthority :
      PointerProbabilityAuthority

    EntropyPathAuthority : Set
    entropyPathAuthority :
      EntropyPathAuthority

    SecondDerivativeAuthority : Set
    secondDerivativeAuthority :
      SecondDerivativeAuthority

open FiniteQuantumProducerAuthority public

record FiniteQuantumProducerStatus : Set where
  field
    partialTraceDefinitionWritten : Bool
    partialTraceDefinitionWrittenIsTrue :
      partialTraceDefinitionWritten ≡ true

    tracePreservationWritten : Bool
    tracePreservationWrittenIsTrue :
      tracePreservationWritten ≡ true

    hermitianPreservationWritten : Bool
    hermitianPreservationWrittenIsTrue :
      hermitianPreservationWritten ≡ true

    positivityPreservationWritten : Bool
    positivityPreservationWrittenIsTrue :
      positivityPreservationWritten ≡ true

    unitaryDensityEvolutionWritten : Bool
    unitaryDensityEvolutionWrittenIsTrue :
      unitaryDensityEvolutionWritten ≡ true

    derivativeBackedEntropyAccelerationWritten : Bool
    derivativeBackedEntropyAccelerationWrittenIsTrue :
      derivativeBackedEntropyAccelerationWritten ≡ true

    exactHeadLeanKernelReceiptPresent : Bool
    exactHeadLeanKernelReceiptPresentIsFalse :
      exactHeadLeanKernelReceiptPresent ≡ false

    HamiltonianExponentialGeneratorPaid : Bool
    HamiltonianExponentialGeneratorPaidIsFalse :
      HamiltonianExponentialGeneratorPaid ≡ false

    CPOEigenprojectorConstructionPaid : Bool
    CPOEigenprojectorConstructionPaidIsFalse :
      CPOEigenprojectorConstructionPaid ≡ false

canonicalFiniteQuantumProducerStatus : FiniteQuantumProducerStatus
canonicalFiniteQuantumProducerStatus = record
  { partialTraceDefinitionWritten = true
  ; partialTraceDefinitionWrittenIsTrue = refl
  ; tracePreservationWritten = true
  ; tracePreservationWrittenIsTrue = refl
  ; hermitianPreservationWritten = true
  ; hermitianPreservationWrittenIsTrue = refl
  ; positivityPreservationWritten = true
  ; positivityPreservationWrittenIsTrue = refl
  ; unitaryDensityEvolutionWritten = true
  ; unitaryDensityEvolutionWrittenIsTrue = refl
  ; derivativeBackedEntropyAccelerationWritten = true
  ; derivativeBackedEntropyAccelerationWrittenIsTrue = refl
  ; exactHeadLeanKernelReceiptPresent = false
  ; exactHeadLeanKernelReceiptPresentIsFalse = refl
  ; HamiltonianExponentialGeneratorPaid = false
  ; HamiltonianExponentialGeneratorPaidIsFalse = refl
  ; CPOEigenprojectorConstructionPaid = false
  ; CPOEigenprojectorConstructionPaidIsFalse = refl
  }

leanReducedStateSourceReceipt : Sources.AttributionReceipt
leanReducedStateSourceReceipt =
  Sources.attribution-receipt
    Sources.importedFormalTheoremSource
    "DASHI Lean: RequestProject.QuantumMereologyReducedState"
    "Source-written finite partial trace and reduced-density owner; includes trace, Hermitian, and positive-semidefinite preservation. Source lineage only until exact-head Lean kernel evidence exists."

leanDensityEvolutionSourceReceipt : Sources.AttributionReceipt
leanDensityEvolutionSourceReceipt =
  Sources.attribution-receipt
    Sources.importedFormalTheoremSource
    "DASHI Lean: RequestProject.QuantumMereologyDensityEvolution"
    "Source-written unitary density-conjugation owner using mathlib unitary, trace, and positivity theorems. Source lineage only until exact-head Lean kernel evidence exists."

leanEntropyAccelerationSourceReceipt : Sources.AttributionReceipt
leanEntropyAccelerationSourceReceipt =
  Sources.attribution-receipt
    Sources.importedFormalTheoremSource
    "DASHI Lean: RequestProject.QuantumMereologyEntropyAcceleration"
    "Source-written entropy-path owner requiring actual HasDerivAt witnesses for both Carroll--Singh t=0 entropy accelerations. Source lineage only until exact-head Lean kernel evidence exists."

dashiFiniteQuantumProducerCrossProverReceipt : Sources.AttributionReceipt
dashiFiniteQuantumProducerCrossProverReceipt =
  Sources.attribution-receipt
    Sources.crossModuleInference
    "DASHI Agda"
    "Aggregates only explicit Lean theorem-source authorities for the finite quantum producer and keeps Hamiltonian exponential generation, CPO eigenprojectors, physical authority, and exact-head kernel certification separate."
