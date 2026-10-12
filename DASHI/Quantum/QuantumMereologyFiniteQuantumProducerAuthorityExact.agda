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
-- * derivative-backed t=0 entropy accelerations,
-- * a constructive finite coordinate-projector family with Hermitian,
--   idempotent, pairwise-orthogonal, complete and diagonal spectral laws,
-- * the pinned mathlib v4.28 finite Hermitian spectral theorem: orthonormal
--   eigenbasis, real eigenvalues and unitary diagonalisation for every concrete
--   finite Hermitian complex matrix.
--
-- The remaining CPO seam is not finite spectral existence.  It is the
-- same-object bridge from the generic selected CPO factor linear map to a
-- concrete Hermitian matrix representative on which that spectral theorem is
-- applied.
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

    HamiltonianExponentialGeneratorSourceWritten : Bool
    HamiltonianExponentialGeneratorSourceWrittenIsTrue :
      HamiltonianExponentialGeneratorSourceWritten ≡ true

    ExponentialDerivativeSpineSourceWritten : Bool
    ExponentialDerivativeSpineSourceWrittenIsTrue :
      ExponentialDerivativeSpineSourceWritten ≡ true

    RealTimeDerivativeRestrictionSourceWritten : Bool
    RealTimeDerivativeRestrictionSourceWrittenIsTrue :
      RealTimeDerivativeRestrictionSourceWritten ≡ true

    StandardBasisProjectorFamilySourceWritten : Bool
    StandardBasisProjectorFamilySourceWrittenIsTrue :
      StandardBasisProjectorFamilySourceWritten ≡ true

    DiagonalSpectralProjectorLawSourceWritten : Bool
    DiagonalSpectralProjectorLawSourceWrittenIsTrue :
      DiagonalSpectralProjectorLawSourceWritten ≡ true

    FiniteHermitianSpectralBasisSourceWritten : Bool
    FiniteHermitianSpectralBasisSourceWrittenIsTrue :
      FiniteHermitianSpectralBasisSourceWritten ≡ true

    ArbitrarySelectedCPOEigenbasisPaid : Bool
    ArbitrarySelectedCPOEigenbasisPaidIsFalse :
      ArbitrarySelectedCPOEigenbasisPaid ≡ false

    SameObjectCPOChartAttachmentAutomatic : Bool
    SameObjectCPOChartAttachmentAutomaticIsFalse :
      SameObjectCPOChartAttachmentAutomatic ≡ false

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
  ; HamiltonianExponentialGeneratorSourceWritten = true
  ; HamiltonianExponentialGeneratorSourceWrittenIsTrue = refl
  ; ExponentialDerivativeSpineSourceWritten = true
  ; ExponentialDerivativeSpineSourceWrittenIsTrue = refl
  ; RealTimeDerivativeRestrictionSourceWritten = true
  ; RealTimeDerivativeRestrictionSourceWrittenIsTrue = refl
  ; StandardBasisProjectorFamilySourceWritten = true
  ; StandardBasisProjectorFamilySourceWrittenIsTrue = refl
  ; DiagonalSpectralProjectorLawSourceWritten = true
  ; DiagonalSpectralProjectorLawSourceWrittenIsTrue = refl
  ; FiniteHermitianSpectralBasisSourceWritten = true
  ; FiniteHermitianSpectralBasisSourceWrittenIsTrue = refl
  ; ArbitrarySelectedCPOEigenbasisPaid = false
  ; ArbitrarySelectedCPOEigenbasisPaidIsFalse = refl
  ; SameObjectCPOChartAttachmentAutomatic = false
  ; SameObjectCPOChartAttachmentAutomaticIsFalse = refl
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

leanStandardBasisProjectorSourceReceipt : Sources.AttributionReceipt
leanStandardBasisProjectorSourceReceipt =
  Sources.attribution-receipt
    Sources.importedFormalTheoremSource
    "DASHI Lean: RequestProject.QuantumMereologyStandardBasisProjector"
    "Source-written finite coordinate rank-one projectors with Hermitian, idempotent, pairwise-orthogonal, complete and diagonal spectral laws, plus the pinned mathlib v4.28 finite-Hermitian orthonormal eigenbasis/unitary spectral theorem. The remaining selected-CPO obligation is the same-object bridge from the generic factor linear map to a concrete Hermitian matrix representative."

dashiFiniteQuantumProducerCrossProverReceipt : Sources.AttributionReceipt
dashiFiniteQuantumProducerCrossProverReceipt =
  Sources.attribution-receipt
    Sources.crossModuleInference
    "DASHI Agda"
    "Aggregates explicit Lean theorem-source authorities for the finite quantum producer. Coordinate projector algebra and finite Hermitian spectral existence are source-written; selected-CPO same-object matrix attachment, physical authority, and exact-head kernel certification remain separate."

leanHamiltonianExponentialSourceReceipt : Sources.AttributionReceipt
leanHamiltonianExponentialSourceReceipt =
  Sources.attribution-receipt
    Sources.importedFormalTheoremSource
    "DASHI Lean: RequestProject.QuantumMereologyHamiltonianExponential"
    "Source-written Hermitian-matrix to unitary exponential path using an explicitly pinned mathlib L2-operator C*-norm and exp_mem_unitary_of_mem_skewAdjoint. Source lineage only until exact-head Lean kernel evidence exists."

leanExponentialDerivativeSourceReceipt : Sources.AttributionReceipt
leanExponentialDerivativeSourceReceipt =
  Sources.attribution-receipt
    Sources.importedFormalTheoremSource
    "DASHI Lean: RequestProject.QuantumMereologyExponentialDerivative"
    "Source-written first/second exponential derivative spine using mathlib hasDerivAt_exp_smul_const plus explicit complex-to-real Fréchet restriction. Source lineage only until exact-head Lean kernel evidence exists."
