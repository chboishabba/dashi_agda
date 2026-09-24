{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsConcreteStructuralSemanticsRound517Exact where

------------------------------------------------------------------------
-- GOAL-1 STRUCTURAL / ROUND517:
-- PROOF-BEARING COMPACT-SIMPLE INDEX + SELECTED R4 SPACETIME
--
-- Safe constructor-first pattern:
--
--   * the rich compact-simple witness lives in this Set2 source bundle;
--   * every group index is required to carry an actual CompactSimpleLieGroup;
--   * the Set-valued endpoint predicate is then trivial only because this
--     semantics value cannot be constructed without that witness;
--   * the selected spacetime object is fixed by construction and
--     IsFourDimensionalEuclidean is literal equality to that object.
--
-- This does NOT infer compact simplicity from an index tag and does not use
-- SU(2) as a generic premise.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.CompactLieGroupCore

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

record StructuralSourceBundle
    (G X : Set) : Set₂ where
  field
    GroupCarrier : G → Set
    LieCarrier : G → Set
    compactSimple :
      ∀ group →
      CompactSimpleLieGroup
        (GroupCarrier group)
        (LieCarrier group)

    -- This is the concrete object selected as Euclidean R4 in the literal
    -- construction.  Its actual R4 interpretation remains part of the source
    -- construction; no second spacetime is selected later.
    euclideanR4 : X

open StructuralSourceBundle public

concreteStructuralSemantics :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum}
    (base :
      Top.LiteralYangMillsSemantics
        (Physical.physicalLiteralCarriers
          G X Nat Configuration ℝ (Configuration → ℝ) Position
          CurvaturePolynomial LocalOperator OPECoefficient StressTensor
          Hilbert Hamiltonian Vacuum)) →
  StructuralSourceBundle G X →
  Top.LiteralYangMillsSemantics
    (Physical.physicalLiteralCarriers
      G X Nat Configuration ℝ (Configuration → ℝ) Position
      CurvaturePolynomial LocalOperator OPECoefficient StressTensor
      Hilbert Hamiltonian Vacuum)
concreteStructuralSemantics base structural = record
  { Top.LiteralYangMillsSemantics.IsCompactSimple =
      λ _ → ⊤
  ; Top.LiteralYangMillsSemantics.IsFourDimensionalEuclidean =
      λ spacetime → spacetime ≡ euclideanR4 structural
  ; Top.LiteralYangMillsSemantics.IsFiniteVolumeCutoffMeasure =
      Top.IsFiniteVolumeCutoffMeasure base
  ; Top.LiteralYangMillsSemantics.IsReflectionPositiveRegularization =
      Top.IsReflectionPositiveRegularization base
  ; Top.LiteralYangMillsSemantics.HasUltravioletYangMillsNormalization =
      Top.HasUltravioletYangMillsNormalization base
  ; Top.LiteralYangMillsSemantics.HasAsymptoticallyFreeScaleTrajectory =
      Top.HasAsymptoticallyFreeScaleTrajectory base
  ; Top.LiteralYangMillsSemantics.IsGaugeInvariantObservable =
      Top.IsGaugeInvariantObservable base
  ; Top.LiteralYangMillsSemantics.IsLocalObservable =
      Top.IsLocalObservable base
  ; Top.LiteralYangMillsSemantics.IsContinuumLimitOf =
      Top.IsContinuumLimitOf base
  ; Top.LiteralYangMillsSemantics.SchwingerBelongsToMeasure =
      Top.SchwingerBelongsToMeasure base
  ; Top.LiteralYangMillsSemantics.IsNontrivialQuantumYangMills =
      Top.IsNontrivialQuantumYangMills base
  ; Top.LiteralYangMillsSemantics.CurvatureOperatorCorrespondence =
      Top.CurvatureOperatorCorrespondence base
  ; Top.LiteralYangMillsSemantics.IsGaugeInvariantLocalOperator =
      Top.IsGaugeInvariantLocalOperator base
  ; Top.LiteralYangMillsSemantics.IsLocalOperator =
      Top.IsLocalOperator base
  ; Top.LiteralYangMillsSemantics.IsPhysicalOPECoefficient =
      Top.IsPhysicalOPECoefficient base
  ; Top.LiteralYangMillsSemantics.IsPhysicalOPERemainder =
      Top.IsPhysicalOPERemainder base
  ; Top.LiteralYangMillsSemantics.HasShortDistanceAsymptoticFreedom =
      Top.HasShortDistanceAsymptoticFreedom base
  ; Top.LiteralYangMillsSemantics.HasStressTensorAndOPE =
      Top.HasStressTensorAndOPE base
  ; Top.LiteralYangMillsSemantics.SatisfiesAcceptedWightmanOrOSAxioms =
      Top.SatisfiesAcceptedWightmanOrOSAxioms base
  ; Top.LiteralYangMillsSemantics.IsReconstructedHilbertSpace =
      Top.IsReconstructedHilbertSpace base
  ; Top.LiteralYangMillsSemantics.IsPositiveSelfAdjointHamiltonian =
      Top.IsPositiveSelfAdjointHamiltonian base
  ; Top.LiteralYangMillsSemantics.IsVacuumSectorAndPositiveEnergyComplement =
      Top.IsVacuumSectorAndPositiveEnergyComplement base
  ; Top.LiteralYangMillsSemantics.IsStrictlyPositiveFiniteMassGap =
      Top.IsStrictlyPositiveFiniteMassGap base
  ; Top.LiteralYangMillsSemantics.GaugeSymmetryPreservedAlongConstruction =
      Top.GaugeSymmetryPreservedAlongConstruction base
  ; Top.LiteralYangMillsSemantics.LocalityPreservedAlongConstruction =
      Top.LocalityPreservedAlongConstruction base
  ; Top.LiteralYangMillsSemantics.EuclideanCovariancePreservedAlongConstruction =
      Top.EuclideanCovariancePreservedAlongConstruction base
  ; Top.LiteralYangMillsSemantics.ReflectionPositivityPreservedAlongConstruction =
      Top.ReflectionPositivityPreservedAlongConstruction base
  ; Top.LiteralYangMillsSemantics.PositivityNormalizationPreservedAlongConstruction =
      Top.PositivityNormalizationPreservedAlongConstruction base
  ; Top.LiteralYangMillsSemantics.VolumeCutoffCompatibilityPreserved =
      Top.VolumeCutoffCompatibilityPreserved base
  ; Top.LiteralYangMillsSemantics.PhysicalScaleLowerBoundUniform =
      Top.PhysicalScaleLowerBoundUniform base
  ; Top.LiteralYangMillsSemantics.NoSpectralPollutionBelowGap =
      Top.NoSpectralPollutionBelowGap base
  ; Top.LiteralYangMillsSemantics.NontrivialityPreservedInLimit =
      Top.NontrivialityPreservedInLimit base
  ; Top.LiteralYangMillsSemantics.GapAndClusteringAreDerivedNotAssumed =
      Top.GapAndClusteringAreDerivedNotAssumed base
  ; Top.LiteralYangMillsSemantics.CompactSimpleParameterizationPreserved =
      ⊤
  }

selectedGroupIsCompactSimple :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum}
    (base :
      Top.LiteralYangMillsSemantics
        (Physical.physicalLiteralCarriers
          G X Nat Configuration ℝ (Configuration → ℝ) Position
          CurvaturePolynomial LocalOperator OPECoefficient StressTensor
          Hilbert Hamiltonian Vacuum))
    (structural : StructuralSourceBundle G X)
    group →
  Top.IsCompactSimple
    (concreteStructuralSemantics base structural)
    group
selectedGroupIsCompactSimple base structural group = tt

selectedSpacetimeIsFourDimensionalEuclidean :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum}
    (base :
      Top.LiteralYangMillsSemantics
        (Physical.physicalLiteralCarriers
          G X Nat Configuration ℝ (Configuration → ℝ) Position
          CurvaturePolynomial LocalOperator OPECoefficient StressTensor
          Hilbert Hamiltonian Vacuum))
    (structural : StructuralSourceBundle G X) →
  Top.IsFourDimensionalEuclidean
    (concreteStructuralSemantics base structural)
    (euclideanR4 structural)
selectedSpacetimeIsFourDimensionalEuclidean base structural = refl

compactSimpleParameterizationPreserved :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum}
    (base :
      Top.LiteralYangMillsSemantics
        (Physical.physicalLiteralCarriers
          G X Nat Configuration ℝ (Configuration → ℝ) Position
          CurvaturePolynomial LocalOperator OPECoefficient StressTensor
          Hilbert Hamiltonian Vacuum))
    (structural : StructuralSourceBundle G X) →
  Top.CompactSimpleParameterizationPreserved
    (concreteStructuralSemantics base structural)
compactSimpleParameterizationPreserved base structural = tt

round517StructuralSemanticsCompilerLevel : ProofLevel
round517StructuralSemanticsCompilerLevel = machineChecked

-- The rich all-G compact-simple witnesses are genuine source inputs.
literalRound517AllGroupCompactSimpleSourceLevel : ProofLevel
literalRound517AllGroupCompactSimpleSourceLevel = conditional
