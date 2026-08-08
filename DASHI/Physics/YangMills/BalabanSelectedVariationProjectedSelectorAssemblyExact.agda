module DASHI.Physics.YangMills.BalabanSelectedVariationProjectedSelectorAssemblyExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Jerrold E. Marsden and Matthew West,
-- "Discrete Mechanics and Variational Integrators",
-- Acta Numerica 10 (2001), 357--514.
-- DOI: 10.1017/S096249290100006X.
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 605--636.
-- DOI: 10.1007/BF01229381.
--
-- DASHI CONTRIBUTION
--
-- Compose the two Round-37 proof lanes on one literal projected variation.
-- `ProjectionSpilloverData` owns the physical mask, finite first-variation
-- covector, raw singleton identity, projector-defect pairing and the exact
-- coefficient split.  This module adds gauge/constraint/locality/charge data
-- and a Noether residual split for that same projected vector, then constructs
-- the Round-37 `ProjectedSingletonConstruction`, the Round-36
-- `SingletonExtractionWitness`, and the selected-background selector.
--
-- No independently supplied spillover equality or bound remains in the
-- assembly interface.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateProjectorExact as Projector
import DASHI.Physics.YangMills.BalabanP33PlaquetteBoundaryProjectorExact as Boundary
import DASHI.Physics.YangMills.BalabanSelectedVariationProjectionSpilloverExact as Spillover
import DASHI.Physics.YangMills.BalabanSelectedVariationProjectedNoetherResidualExact as Noether
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonSignedGlobalExact as Wilson

record ProjectedSelectorAnalyticData
    (background : Physical.RationalSU2Background4)
    (field : Coordinates.PhysicalSU2BondField4)
    (plaquette : Physical.Plaquette4) : Set₁ where
  field
    spilloverData :
      Spillover.ProjectionSpilloverData background field plaquette

    GaugeAdmissible : Projector.PhysicalVector → Set
    ConstraintTangent : Projector.PhysicalVector → Set
    SupportedNearPlaquette : Projector.PhysicalVector → Set

    projectedGaugeAdmissible :
      GaugeAdmissible
        (Projector.physicalCoordinateProject
          (Spillover.physicalHodgeMask spilloverData)
          (Boundary.rawPlaquetteSingletonExtractor field plaquette))

    projectedConstraintTangent :
      ConstraintTangent
        (Projector.physicalCoordinateProject
          (Spillover.physicalHodgeMask spilloverData)
          (Boundary.rawPlaquetteSingletonExtractor field plaquette))

    projectedLocal :
      SupportedNearPlaquette
        (Projector.physicalCoordinateProject
          (Spillover.physicalHodgeMask spilloverData)
          (Boundary.rawPlaquetteSingletonExtractor field plaquette))

    selectorConstant : ℚ
    selectorConstantNonnegative : 0ℚ ≤ selectorConstant

    projectedVariationChargeBound :
      Coordinates.physicalSU2CoordinateNormSq
        (Projector.physicalCoordinateProject
          (Spillover.physicalHodgeMask spilloverData)
          (Boundary.rawPlaquetteSingletonExtractor field plaquette))
      ≤ selectorConstant
        * Wilson.plaquetteCrossCharge field plaquette

    gaugeResidual : ℚ
    constraintResidual : ℚ
    selectedEulerResidual : ℚ

    selectedVariationFirstVariationResidualSplit :
      Spillover.firstVariationFromCovector
        (Spillover.firstVariationCovector spilloverData)
        (Projector.physicalCoordinateProject
          (Spillover.physicalHodgeMask spilloverData)
          (Boundary.rawPlaquetteSingletonExtractor field plaquette))
      ≡ gaugeResidual + constraintResidual + selectedEulerResidual

    gaugeVerticalResidualVanishes : gaugeResidual ≡ 0ℚ
    constraintNormalResidualVanishes : constraintResidual ≡ 0ℚ
    selectedEulerResidualVanishes : selectedEulerResidual ≡ 0ℚ

open ProjectedSelectorAnalyticData public

analyticDataToProjectedSingletonConstruction :
  ∀ {background field plaquette} →
  ProjectedSelectorAnalyticData background field plaquette →
  Noether.ProjectedSingletonConstruction background field plaquette
analyticDataToProjectedSingletonConstruction
    {background} {field} {plaquette} data =
  let spill = spilloverData data in
  record
    { Noether.ProjectedSingletonConstruction.physicalHodgeMask =
        Spillover.physicalHodgeMask spill
    ; Noether.ProjectedSingletonConstruction.GaugeAdmissible =
        GaugeAdmissible data
    ; Noether.ProjectedSingletonConstruction.ConstraintTangent =
        ConstraintTangent data
    ; Noether.ProjectedSingletonConstruction.SupportedNearPlaquette =
        SupportedNearPlaquette data
    ; Noether.ProjectedSingletonConstruction.projectedGaugeAdmissible =
        projectedGaugeAdmissible data
    ; Noether.ProjectedSingletonConstruction.projectedConstraintTangent =
        projectedConstraintTangent data
    ; Noether.ProjectedSingletonConstruction.projectedLocal =
        projectedLocal data
    ; Noether.ProjectedSingletonConstruction.selectorConstant =
        selectorConstant data
    ; Noether.ProjectedSingletonConstruction.selectorConstantNonnegative =
        selectorConstantNonnegative data
    ; Noether.ProjectedSingletonConstruction.projectedVariationChargeBound =
        projectedVariationChargeBound data
    ; Noether.ProjectedSingletonConstruction.firstVariation =
        Spillover.firstVariationFromCovector
          (Spillover.firstVariationCovector spill)
    ; Noether.ProjectedSingletonConstruction.gaugeResidual =
        gaugeResidual data
    ; Noether.ProjectedSingletonConstruction.constraintResidual =
        constraintResidual data
    ; Noether.ProjectedSingletonConstruction.selectedEulerResidual =
        selectedEulerResidual data
    ; Noether.ProjectedSingletonConstruction.projectorLocalizationResidual =
        Spillover.projectedExtractionSpillover spill
    ; Noether.ProjectedSingletonConstruction.selectedVariationFirstVariationResidualSplit =
        selectedVariationFirstVariationResidualSplit data
    ; Noether.ProjectedSingletonConstruction.gaugeVerticalResidualVanishes =
        gaugeVerticalResidualVanishes data
    ; Noether.ProjectedSingletonConstruction.constraintNormalResidualVanishes =
        constraintNormalResidualVanishes data
    ; Noether.ProjectedSingletonConstruction.selectedEulerResidualVanishes =
        selectedEulerResidualVanishes data
    ; Noether.ProjectedSingletonConstruction.localizationResidualIsSingletonSpillover =
        Spillover.projectedExtractorIdentity spill
    ; Noether.ProjectedSingletonConstruction.projectorLocalizationSpilloverUpper =
        Spillover.projectedExtractionSpilloverUpper spill
    }

analyticDataToSingletonExtractionWitness :
  ∀ {background field plaquette} →
  ProjectedSelectorAnalyticData background field plaquette →
  Selector.SingletonExtractionWitness background field plaquette
analyticDataToSingletonExtractionWitness data =
  Noether.projectedConstructionToSingletonWitness
    (analyticDataToProjectedSingletonConstruction data)

record ProjectedSelectorAnalyticFamily
    (background : Physical.RationalSU2Background4)
    (field : Coordinates.PhysicalSU2BondField4) : Set₁ where
  field
    construct : ∀ plaquette →
      ProjectedSelectorAnalyticData background field plaquette

open ProjectedSelectorAnalyticFamily public

analyticFamilyToSelectedBackgroundVariationSelector :
  ∀ {background field} →
  ProjectedSelectorAnalyticFamily background field →
  Selector.SelectedBackgroundVariationSelector background field
analyticFamilyToSelectedBackgroundVariationSelector family =
  record
    { Selector.SelectedBackgroundVariationSelector.select =
        λ plaquette →
          analyticDataToSingletonExtractionWitness
            (construct family plaquette)
    }

analyticDataGivesSingletonLower :
  ∀ {background field plaquette} →
  ProjectedSelectorAnalyticData background field plaquette →
  - (Selector.remainingSingletonCoefficient
      * Wilson.plaquetteCrossCharge field plaquette)
  ≤ Noether.Partition.physicalPlaquetteWilsonLinearPart
      background field plaquette
analyticDataGivesSingletonLower data =
  Selector.selectedBackgroundSingletonCurvatureLower
    (analyticDataToSingletonExtractionWitness data)

projectedSelectorAssemblyLevel : ProofLevel
projectedSelectorAssemblyLevel = machineChecked

projectedSelectorSpilloverCompatibilityLevel : ProofLevel
projectedSelectorSpilloverCompatibilityLevel = machineChecked
