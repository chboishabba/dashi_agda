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
-- * explicit finite bipartite partial traces with density-law preservation,
-- * unitary conjugation preserving density-matrix laws,
-- * finite pointer-projector trace readouts,
-- * coordinate-projector Born probabilities proved nonnegative and normalized,
-- * linear and pointer entropy paths and derivative-backed accelerations,
-- * coordinate-projector Hermitian/idempotent/orthogonal/complete laws,
-- * pinned mathlib finite-Hermitian spectral bases/unitary diagonalisation,
-- * a same-selected-CPO finite-Hermitian refinement from supplied literal
--   LinearMap.IsSymmetric factor witnesses,
-- * under that refinement, native factor eigenbases tensor to an orthonormal
--   eigenbasis of the exact selected product CPO with product eigenvalues,
-- * finite spectral von Neumann entropy and both bipartite reduced density
--   matrices, hence same-object bipartite mutual information,
-- * finite nonempty Schwinger-search minimizer existence.
--
-- The physics/source firewalls remain explicit. Coordinate Born closure does
-- not identify the coordinate basis with the physical selected-CPO pointer
-- basis. The generic CPO Hermitian labels do not create literal symmetry.
-- The typed product-CPO eigenbasis is conditional on that stronger symmetry
-- refinement and is not promoted to an empirically validated pointer basis.
-- Bipartite mutual information does not by itself produce an N-factor graph,
-- metric, MDS embedding, curvature or spacetime. Finite minimizer existence
-- does not establish that the source search is finite/nonempty, unique, or the
-- unrestricted physical global optimum.
--
-- Agda records Lean results only as source-written/imported theorem authority
-- until an exact-head Lean kernel receipt is separately available.
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

    TypedSelectedCPOFiniteHermitianRefinementSourceWritten : Bool
    TypedSelectedCPOFiniteHermitianRefinementSourceWrittenIsTrue :
      TypedSelectedCPOFiniteHermitianRefinementSourceWritten ≡ true

    TypedSelectedCPOProductEigenbasisSourceWritten : Bool
    TypedSelectedCPOProductEigenbasisSourceWrittenIsTrue :
      TypedSelectedCPOProductEigenbasisSourceWritten ≡ true

    GenericCPOAdmissibilityCreatesTypedSymmetry : Bool
    GenericCPOAdmissibilityCreatesTypedSymmetryIsFalse :
      GenericCPOAdmissibilityCreatesTypedSymmetry ≡ false

    CoordinateBornProbabilityNonnegativeSourceWritten : Bool
    CoordinateBornProbabilityNonnegativeSourceWrittenIsTrue :
      CoordinateBornProbabilityNonnegativeSourceWritten ≡ true

    CoordinateBornProbabilityNormalizedSourceWritten : Bool
    CoordinateBornProbabilityNormalizedSourceWrittenIsTrue :
      CoordinateBornProbabilityNormalizedSourceWritten ≡ true

    CoordinateBornProbabilityCreatesPhysicalPointerIdentification : Bool
    CoordinateBornProbabilityCreatesPhysicalPointerIdentificationIsFalse :
      CoordinateBornProbabilityCreatesPhysicalPointerIdentification ≡ false

    FiniteVonNeumannEntropySourceWritten : Bool
    FiniteVonNeumannEntropySourceWrittenIsTrue :
      FiniteVonNeumannEntropySourceWritten ≡ true

    BipartiteMutualInformationSourceWritten : Bool
    BipartiteMutualInformationSourceWrittenIsTrue :
      BipartiteMutualInformationSourceWritten ≡ true

    CCMDistanceAnsatzSourceAttributed : Bool
    CCMDistanceAnsatzSourceAttributedIsTrue :
      CCMDistanceAnsatzSourceAttributed ≡ true

    CCMDistanceAnsatzCreatesMetric : Bool
    CCMDistanceAnsatzCreatesMetricIsFalse :
      CCMDistanceAnsatzCreatesMetric ≡ false

    BipartiteMutualInformationCreatesNFactorGraph : Bool
    BipartiteMutualInformationCreatesNFactorGraphIsFalse :
      BipartiteMutualInformationCreatesNFactorGraph ≡ false

    FiniteNonemptySchwingerMinimizerSourceWritten : Bool
    FiniteNonemptySchwingerMinimizerSourceWrittenIsTrue :
      FiniteNonemptySchwingerMinimizerSourceWritten ≡ true

    FiniteSchwingerMinimizerCreatesUniqueness : Bool
    FiniteSchwingerMinimizerCreatesUniquenessIsFalse :
      FiniteSchwingerMinimizerCreatesUniqueness ≡ false

    SourceSchwingerSearchAutomaticallyFiniteNonempty : Bool
    SourceSchwingerSearchAutomaticallyFiniteNonemptyIsFalse :
      SourceSchwingerSearchAutomaticallyFiniteNonempty ≡ false

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
  ; TypedSelectedCPOFiniteHermitianRefinementSourceWritten = true
  ; TypedSelectedCPOFiniteHermitianRefinementSourceWrittenIsTrue = refl
  ; TypedSelectedCPOProductEigenbasisSourceWritten = true
  ; TypedSelectedCPOProductEigenbasisSourceWrittenIsTrue = refl
  ; GenericCPOAdmissibilityCreatesTypedSymmetry = false
  ; GenericCPOAdmissibilityCreatesTypedSymmetryIsFalse = refl
  ; CoordinateBornProbabilityNonnegativeSourceWritten = true
  ; CoordinateBornProbabilityNonnegativeSourceWrittenIsTrue = refl
  ; CoordinateBornProbabilityNormalizedSourceWritten = true
  ; CoordinateBornProbabilityNormalizedSourceWrittenIsTrue = refl
  ; CoordinateBornProbabilityCreatesPhysicalPointerIdentification = false
  ; CoordinateBornProbabilityCreatesPhysicalPointerIdentificationIsFalse = refl
  ; FiniteVonNeumannEntropySourceWritten = true
  ; FiniteVonNeumannEntropySourceWrittenIsTrue = refl
  ; BipartiteMutualInformationSourceWritten = true
  ; BipartiteMutualInformationSourceWrittenIsTrue = refl
  ; CCMDistanceAnsatzSourceAttributed = true
  ; CCMDistanceAnsatzSourceAttributedIsTrue = refl
  ; CCMDistanceAnsatzCreatesMetric = false
  ; CCMDistanceAnsatzCreatesMetricIsFalse = refl
  ; BipartiteMutualInformationCreatesNFactorGraph = false
  ; BipartiteMutualInformationCreatesNFactorGraphIsFalse = refl
  ; FiniteNonemptySchwingerMinimizerSourceWritten = true
  ; FiniteNonemptySchwingerMinimizerSourceWrittenIsTrue = refl
  ; FiniteSchwingerMinimizerCreatesUniqueness = false
  ; FiniteSchwingerMinimizerCreatesUniquenessIsFalse = refl
  ; SourceSchwingerSearchAutomaticallyFiniteNonempty = false
  ; SourceSchwingerSearchAutomaticallyFiniteNonemptyIsFalse = refl
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
    "Source-written finite coordinate rank-one projectors with Hermitian, idempotent, pairwise-orthogonal, complete and diagonal spectral laws, plus the pinned mathlib v4.28 finite-Hermitian orthonormal eigenbasis/unitary spectral theorem."

leanFiniteHermitianCPORefinementSourceReceipt : Sources.AttributionReceipt
leanFiniteHermitianCPORefinementSourceReceipt =
  Sources.attribution-receipt
    Sources.importedFormalTheoremSource
    "DASHI Lean: RequestProject.QuantumMereologyFiniteHermitianCPO"
    "Source-written same-selected-CPO refinement carrying finite orthonormal factor bases and literal LinearMap.IsSymmetric witnesses. Pinned mathlib compiles those maps to Hermitian matrices and native factor eigenbases; OrthonormalBasis.tensorProduct then yields an orthonormal eigenbasis of the exact selected product CPO with product eigenvalues. Generic source-facing Hermitian labels do not automatically create this stronger refinement, and the mathematical basis is not promoted to an empirically validated pointer basis."

leanBornProbabilitySourceReceipt : Sources.AttributionReceipt
leanBornProbabilitySourceReceipt =
  Sources.attribution-receipt
    Sources.importedFormalTheoremSource
    "DASHI Lean: RequestProject.QuantumMereologyBornProbability"
    "Source-written finite coordinate-projector Born closure: for every PSD trace-one density matrix the coordinate probabilities are diagonal real parts, are nonnegative, and sum to one. This does not identify the coordinate family with a physical selected-CPO pointer basis."

leanVonNeumannInformationSourceReceipt : Sources.AttributionReceipt
leanVonNeumannInformationSourceReceipt =
  Sources.attribution-receipt
    Sources.importedFormalTheoremSource
    "DASHI Lean: RequestProject.QuantumMereologyVonNeumannInformation"
    "Source-written finite spectral von Neumann entropy, density-spectrum probability/nonnegative entropy laws, explicit left/right bipartite partial traces returning density matrices, same-object bipartite mutual information, and nonnegative CCM present-edge length on its declared normalized domain. Cao--Carroll--Michalakis supply only the separately attributed external mutual-information graph/distance claim; the Lean finite matrix implementation is DASHI-owned."

caoCarrollMichalakisDistanceClaim : Sources.AttributionReceipt
caoCarrollMichalakisDistanceClaim =
  Sources.attribution-receipt
    Sources.externalSourceClaim
    "ChunJun Cao; Sean M. Carroll; Spyridon Michalakis, Phys. Rev. D 95, 024031 (2017), arXiv:1606.08444"
    "Uses I(A:B)=S(A)+S(B)-S(AB) as an edge weight and introduces a separate system-dependent decreasing distance ansatz for nonzero mutual information. This source attribution does not constitute a DASHI proof of metric axioms, graph-global consistency, MDS realization, curvature, or spacetime."

leanFiniteSchwingerSelectionSourceReceipt : Sources.AttributionReceipt
leanFiniteSchwingerSelectionSourceReceipt =
  Sources.attribution-receipt
    Sources.importedFormalTheoremSource
    "DASHI Lean: RequestProject.QuantumMereologyFiniteSchwingerSelection"
    "Source-written theorem that a finite candidate carrier with a nonempty admissible subset admits a minimum of the reconstructed real-valued Schwinger score and therefore a PreferredTPSSelectionReceipt. Carroll--Singh are not attributed this finite-order existence theorem; finiteness, admissible nonemptiness, uniqueness, and unrestricted physical optimality remain separate."

dashiFiniteQuantumProducerCrossProverReceipt : Sources.AttributionReceipt
dashiFiniteQuantumProducerCrossProverReceipt =
  Sources.attribution-receipt
    Sources.crossModuleInference
    "DASHI Agda"
    "Aggregates explicit Lean theorem-source authorities for finite quantum mereology. Born closure, finite Hermitian and selected-product CPO spectral structure under typed symmetry, finite von Neumann/mutual-information production, and finite-search minimizer existence are source-written. Generic-CPO-to-typed-symmetry, empirical pointer-basis authority, N-factor information-graph consistency, metric/spatial realization, physical global preference, and exact-head kernel certification remain separate."

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
    "Source-written first/second exponential derivative spine using mathlib hasDerivAt_exp_smul_const plus explicit complex-to-real Frechet restriction. Source lineage only until exact-head Lean kernel evidence exists."
