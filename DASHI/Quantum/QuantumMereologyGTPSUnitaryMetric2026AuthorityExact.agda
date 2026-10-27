{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumMereologyGTPSUnitaryMetric2026AuthorityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Quantum.QuantumMereologySourceAtlasExact as Sources

record GTPSUnitaryMetricStatus : Set where
  field
    UnitaryFamilyMetricFormulaSourceWritten : Bool
    UnitaryFamilyMetricFormulaSourceWrittenIsTrue :
      UnitaryFamilyMetricFormulaSourceWritten ≡ true

    CanonicalFiniteProjectorConsumed : Bool
    CanonicalFiniteProjectorConsumedIsTrue :
      CanonicalFiniteProjectorConsumed ≡ true

    SourceTangentGeneratorEquationExplicit : Bool
    SourceTangentGeneratorEquationExplicitIsTrue :
      SourceTangentGeneratorEquationExplicit ≡ true

    FixedReferenceCommutantDimensionExplicit : Bool
    FixedReferenceCommutantDimensionExplicitIsTrue :
      FixedReferenceCommutantDimensionExplicit ≡ true

    MinimizerMapPullbackDifferentiated : Bool
    MinimizerMapPullbackDifferentiatedIsFalse :
      MinimizerMapPullbackDifferentiated ≡ false

    HamiltonianParameterMetricSourceWritten : Bool
    HamiltonianParameterMetricSourceWrittenIsFalse :
      HamiltonianParameterMetricSourceWritten ≡ false

    AlgebraSusceptibilitySingularitySourceWritten : Bool
    AlgebraSusceptibilitySingularitySourceWrittenIsFalse :
      AlgebraSusceptibilitySingularitySourceWritten ≡ false

    ThermodynamicMQPTSourceWritten : Bool
    ThermodynamicMQPTSourceWrittenIsFalse :
      ThermodynamicMQPTSourceWritten ≡ false

canonicalGTPSUnitaryMetricStatus : GTPSUnitaryMetricStatus
canonicalGTPSUnitaryMetricStatus = record
  { UnitaryFamilyMetricFormulaSourceWritten = true
  ; UnitaryFamilyMetricFormulaSourceWrittenIsTrue = refl
  ; CanonicalFiniteProjectorConsumed = true
  ; CanonicalFiniteProjectorConsumedIsTrue = refl
  ; SourceTangentGeneratorEquationExplicit = true
  ; SourceTangentGeneratorEquationExplicitIsTrue = refl
  ; FixedReferenceCommutantDimensionExplicit = true
  ; FixedReferenceCommutantDimensionExplicitIsTrue = refl
  ; MinimizerMapPullbackDifferentiated = false
  ; MinimizerMapPullbackDifferentiatedIsFalse = refl
  ; HamiltonianParameterMetricSourceWritten = false
  ; HamiltonianParameterMetricSourceWrittenIsFalse = refl
  ; AlgebraSusceptibilitySingularitySourceWritten = false
  ; AlgebraSusceptibilitySingularitySourceWrittenIsFalse = refl
  ; ThermodynamicMQPTSourceWritten = false
  ; ThermodynamicMQPTSourceWrittenIsFalse = refl
  }

zanardiDallasAndreadakisUnitaryMetricExternalClaim : Sources.AttributionReceipt
zanardiDallasAndreadakisUnitaryMetricExternalClaim =
  Sources.attribution-receipt
    Sources.externalSourceClaim
    "Paolo Zanardi; Emanuel Dallas; Faidon Andreadakis, Mereological Quantum Phase Transitions, Phys. Rev. A 113, 042201 (2026), DOI 10.1103/r193-5s7w; arXiv:2510.06389"
    "For A_theta = Ad(U_theta)(A_0), gives ds_Theta^2 = kappa^2 ||Q_theta(dK)||_2^2 with kappa = 2/(dim A'_0) and dK = -i dU_theta U_theta^dagger, then separately pulls this metric through the scrambling-minimizer map and interprets thermodynamic-limit singularities as mereological quantum phase transitions."

leanGTPSUnitaryMetricSourceReceipt : Sources.AttributionReceipt
leanGTPSUnitaryMetricSourceReceipt =
  Sources.attribution-receipt
    Sources.importedFormalTheoremSource
    "DASHI Lean: QuantumMereologyGTPSUnitaryMetric2026"
    "Source-written finite reconstruction of the unitary-family metric element over an explicit tangent receipt and the canonical finite Hilbert--Schmidt projector. The minimizer-map derivative, Hamiltonian-parameter pullback, susceptibility singularity and thermodynamic m-QPT remain unproved."

dashiGTPSUnitaryMetricCrossModuleReceipt : Sources.AttributionReceipt
dashiGTPSUnitaryMetricCrossModuleReceipt =
  Sources.attribution-receipt
    Sources.crossModuleInference
    "DASHI Agda"
    "Records the external-source/formal-reconstruction split without claiming Agda proof replay or promoting the finite metric formula to a physical phase-transition theorem."
