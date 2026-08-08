module DASHI.Physics.YangMills.BalabanSelectedVariationProjectedNoetherResidualExact where

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
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- DASHI CONTRIBUTION
--
-- Replace the opaque selected-variation stationarity field by one same-object
-- projector/residual construction.  A raw plaquette-boundary extractor is
-- projected by a concrete finite coordinate projector.  The first variation
-- is split into uniquely named gauge, constraint and selected-Euler residuals;
-- their separate vanishing proves stationarity.  A second exact equality
-- identifies the same first variation with the literal four-singleton Wilson
-- term plus the owned projector/localization spillover.
--
-- The module constructs the Round-36 SingletonExtractionWitness and the full
-- SelectedBackgroundVariationSelector from this data.  It still does not claim
-- the physical Hodge/gauge projector or the sharp spillover estimate has been
-- produced: those are the remaining analytic inputs, now reduced to explicit
-- fields on one projected variation rather than independent receipts.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; -_; _≤_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateProjectorExact as Projector
import DASHI.Physics.YangMills.BalabanP33PlaquetteBoundaryProjectorExact as Boundary
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonLinearNonlinearPartitionExact as Partition
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonSignedGlobalExact as Wilson
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector

data FirstVariationResidualOwner : Set where
  gaugeVerticalOwner : FirstVariationResidualOwner
  constraintNormalOwner : FirstVariationResidualOwner
  selectedEulerOwner : FirstVariationResidualOwner
  projectorLocalizationOwner : FirstVariationResidualOwner

record ProjectedSingletonConstruction
    (background : Physical.RationalSU2Background4)
    (field : Coordinates.PhysicalSU2BondField4)
    (plaquette : Physical.Plaquette4) : Set₁ where
  field
    physicalHodgeMask : Projector.PhysicalCoordinateMask

    GaugeAdmissible : Projector.PhysicalVector → Set
    ConstraintTangent : Projector.PhysicalVector → Set
    SupportedNearPlaquette : Projector.PhysicalVector → Set

    projectedGaugeAdmissible :
      GaugeAdmissible
        (Projector.physicalCoordinateProject physicalHodgeMask
          (Boundary.rawPlaquetteSingletonExtractor field plaquette))

    projectedConstraintTangent :
      ConstraintTangent
        (Projector.physicalCoordinateProject physicalHodgeMask
          (Boundary.rawPlaquetteSingletonExtractor field plaquette))

    projectedLocal :
      SupportedNearPlaquette
        (Projector.physicalCoordinateProject physicalHodgeMask
          (Boundary.rawPlaquetteSingletonExtractor field plaquette))

    selectorConstant : ℚ
    selectorConstantNonnegative : 0ℚ ≤ selectorConstant

    projectedVariationChargeBound :
      Coordinates.physicalSU2CoordinateNormSq
        (Projector.physicalCoordinateProject physicalHodgeMask
          (Boundary.rawPlaquetteSingletonExtractor field plaquette))
      ≤ selectorConstant * Wilson.plaquetteCrossCharge field plaquette

    firstVariation : Projector.PhysicalVector → ℚ

    gaugeResidual : ℚ
    constraintResidual : ℚ
    selectedEulerResidual : ℚ
    projectorLocalizationResidual : ℚ

    selectedVariationFirstVariationResidualSplit :
      firstVariation
        (Projector.physicalCoordinateProject physicalHodgeMask
          (Boundary.rawPlaquetteSingletonExtractor field plaquette))
      ≡ gaugeResidual + constraintResidual + selectedEulerResidual

    gaugeVerticalResidualVanishes : gaugeResidual ≡ 0ℚ
    constraintNormalResidualVanishes : constraintResidual ≡ 0ℚ
    selectedEulerResidualVanishes : selectedEulerResidual ≡ 0ℚ

    localizationResidualIsSingletonSpillover :
      firstVariation
        (Projector.physicalCoordinateProject physicalHodgeMask
          (Boundary.rawPlaquetteSingletonExtractor field plaquette))
      ≡ Partition.physicalPlaquetteWilsonLinearPart
          background field plaquette
        + projectorLocalizationResidual

    projectorLocalizationSpilloverUpper :
      projectorLocalizationResidual
      ≤ Selector.remainingSingletonCoefficient
          * Wilson.plaquetteCrossCharge field plaquette

open ProjectedSingletonConstruction public

projectedSelectedPlaquetteVariation :
  ∀ {background field plaquette} →
  ProjectedSingletonConstruction background field plaquette →
  Projector.PhysicalVector
projectedSelectedPlaquetteVariation {field = field} {plaquette = plaquette}
    construction =
  Projector.physicalCoordinateProject
    (physicalHodgeMask construction)
    (Boundary.rawPlaquetteSingletonExtractor field plaquette)

residualOwnedBy :
  ∀ {background field plaquette} →
  ProjectedSingletonConstruction background field plaquette →
  FirstVariationResidualOwner → ℚ
residualOwnedBy construction gaugeVerticalOwner =
  gaugeResidual construction
residualOwnedBy construction constraintNormalOwner =
  constraintResidual construction
residualOwnedBy construction selectedEulerOwner =
  selectedEulerResidual construction
residualOwnedBy construction projectorLocalizationOwner =
  projectorLocalizationResidual construction

selectedVariationResidualStationary :
  ∀ {background field plaquette}
    (construction :
      ProjectedSingletonConstruction background field plaquette) →
  firstVariation construction
    (projectedSelectedPlaquetteVariation construction)
  ≡ 0ℚ
selectedVariationResidualStationary construction =
  trans
    (selectedVariationFirstVariationResidualSplit construction)
    (trans
      (cong
        (λ selected →
          selected
          + constraintResidual construction
          + selectedEulerResidual construction)
        (gaugeVerticalResidualVanishes construction))
      (trans
        (cong
          (λ selected →
            0ℚ + selected + selectedEulerResidual construction)
          (constraintNormalResidualVanishes construction))
        (trans
          (cong
            (λ selected → 0ℚ + 0ℚ + selected)
            (selectedEulerResidualVanishes construction))
          (ℚRing.solve []))))

projectedConstructionToSingletonWitness :
  ∀ {background field plaquette} →
  ProjectedSingletonConstruction background field plaquette →
  Selector.SingletonExtractionWitness background field plaquette
projectedConstructionToSingletonWitness
    {background} {field} {plaquette} construction =
  record
    { Selector.SingletonExtractionWitness.FineVariation =
        Projector.PhysicalVector
    ; Selector.SingletonExtractionWitness.variation =
        projectedSelectedPlaquetteVariation construction
    ; Selector.SingletonExtractionWitness.GaugeAdmissible =
        GaugeAdmissible construction
    ; Selector.SingletonExtractionWitness.ConstraintTangent =
        ConstraintTangent construction
    ; Selector.SingletonExtractionWitness.SupportedNearPlaquette =
        SupportedNearPlaquette construction
    ; Selector.SingletonExtractionWitness.gaugeAdmissible =
        projectedGaugeAdmissible construction
    ; Selector.SingletonExtractionWitness.constraintTangent =
        projectedConstraintTangent construction
    ; Selector.SingletonExtractionWitness.localSupport =
        projectedLocal construction
    ; Selector.SingletonExtractionWitness.variationNormSq =
        Coordinates.physicalSU2CoordinateNormSq
    ; Selector.SingletonExtractionWitness.selectorConstant =
        selectorConstant construction
    ; Selector.SingletonExtractionWitness.selectorConstantNonnegative =
        selectorConstantNonnegative construction
    ; Selector.SingletonExtractionWitness.variationChargeBound =
        projectedVariationChargeBound construction
    ; Selector.SingletonExtractionWitness.firstVariation =
        firstVariation construction
    ; Selector.SingletonExtractionWitness.extractionSpillover =
        projectorLocalizationResidual construction
    ; Selector.SingletonExtractionWitness.selectedEulerLagrangeStationary =
        selectedVariationResidualStationary construction
    ; Selector.SingletonExtractionWitness.extractsLiteralSingleton =
        localizationResidualIsSingletonSpillover construction
    ; Selector.SingletonExtractionWitness.spilloverUpper =
        projectorLocalizationSpilloverUpper construction
    }

record ProjectedSelectedVariationFamily
    (background : Physical.RationalSU2Background4)
    (field : Coordinates.PhysicalSU2BondField4) : Set₁ where
  field
    construct : ∀ plaquette →
      ProjectedSingletonConstruction background field plaquette

open ProjectedSelectedVariationFamily public

projectedFamilyToSelectedBackgroundVariationSelector :
  ∀ {background field} →
  ProjectedSelectedVariationFamily background field →
  Selector.SelectedBackgroundVariationSelector background field
projectedFamilyToSelectedBackgroundVariationSelector family =
  record
    { Selector.SelectedBackgroundVariationSelector.select =
        λ plaquette →
          projectedConstructionToSingletonWitness
            (construct family plaquette)
    }

projectedSelectorGivesSingletonLower :
  ∀ {background field plaquette} →
  ProjectedSingletonConstruction background field plaquette →
  - (Selector.remainingSingletonCoefficient
      * Wilson.plaquetteCrossCharge field plaquette)
  ≤ Partition.physicalPlaquetteWilsonLinearPart
      background field plaquette
projectedSelectorGivesSingletonLower construction =
  Selector.selectedBackgroundSingletonCurvatureLower
    (projectedConstructionToSingletonWitness construction)

projectedNoetherResidualReducerLevel : ProofLevel
projectedNoetherResidualReducerLevel = machineChecked

projectedBoundaryExtractorLevel : ProofLevel
projectedBoundaryExtractorLevel = machineChecked

physicalHodgeGaugeProjectorConstructionLevel : ProofLevel
physicalHodgeGaugeProjectorConstructionLevel = conditional

projectorLocalizationSpilloverLevel : ProofLevel
projectorLocalizationSpilloverLevel = conditional
