module DASHI.Physics.YangMills.BalabanSelectedVariationProjectionSpilloverExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Jerrold E. Marsden and Matthew West,
-- "Discrete Mechanics and Variational Integrators",
-- Acta Numerica 10 (2001), 357--514.
-- DOI: 10.1017/S096249290100006X.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 605--636.
-- DOI: 10.1007/BF01229381.
--
-- DASHI CONTRIBUTION
--
-- Make the Hodge/projector spillover algebra literal.  A first variation is a
-- finite covector paired with the physical coordinate state.  For any mask P
-- and raw local extractor w, define the discarded component (I-P)w.  Exact
-- finite rational summation proves
--
--   dA(Pw) = dA(w) - dA((I-P)w).
--
-- If the raw extractor gives the singleton term plus a raw localization
-- residual, then the projected extractor gives the singleton term plus
--
--   raw residual - projector-defect pairing.
--
-- Separate upper bounds on those two owned terms combine into the exact
-- Round-36 coefficient.  The physical estimates themselves remain the
-- frontier; the decomposition and budget composition are proved here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; _+_; _-_; _*_; -_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateProjectorExact as Projector
import DASHI.Physics.YangMills.BalabanP33PlaquetteBoundaryProjectorExact as Boundary
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Plaquette
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonLinearNonlinearPartitionExact as Partition
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonSignedGlobalExact as Wilson
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector

PhysicalVector : Set
PhysicalVector = Projector.PhysicalVector

vectorSubtract : PhysicalVector → PhysicalVector → PhysicalVector
vectorSubtract left right coordinate = left coordinate - right coordinate

projectorDiscardedComponent :
  Projector.PhysicalCoordinateMask →
  PhysicalVector → PhysicalVector
projectorDiscardedComponent mask vector =
  vectorSubtract vector
    (Projector.physicalCoordinateProject mask vector)

firstVariationFromCovector :
  PhysicalVector → PhysicalVector → ℚ
firstVariationFromCovector covector vector =
  Physical.physicalCoordinateDot covector vector

rawEqualsProjectedPlusDiscardedPointwise :
  ∀ mask vector coordinate →
  vector coordinate
  ≡ Projector.physicalCoordinateProject mask vector coordinate
    + projectorDiscardedComponent mask vector coordinate
rawEqualsProjectedPlusDiscardedPointwise mask vector coordinate
  with mask coordinate
... | false = ℚRing.solve-∀ (vector coordinate)
... | true = ℚRing.solve-∀ (vector coordinate)

firstVariationRawSplitsProjectedDiscarded :
  ∀ covector mask vector →
  firstVariationFromCovector covector vector
  ≡ firstVariationFromCovector covector
      (Projector.physicalCoordinateProject mask vector)
    + firstVariationFromCovector covector
      (projectorDiscardedComponent mask vector)
firstVariationRawSplitsProjectedDiscarded covector mask vector =
  trans
    (Sums.sumRationalCong
      Physical.physicalSU2Coordinates4
      (λ coordinate → covector coordinate * vector coordinate)
      (λ coordinate →
        covector coordinate
          * (Projector.physicalCoordinateProject mask vector coordinate
            + projectorDiscardedComponent mask vector coordinate))
      (λ coordinate →
        cong (covector coordinate *_)
          (rawEqualsProjectedPlusDiscardedPointwise
            mask vector coordinate)))
    (trans
      (Sums.sumRationalCong
        Physical.physicalSU2Coordinates4
        (λ coordinate →
          covector coordinate
            * (Projector.physicalCoordinateProject mask vector coordinate
              + projectorDiscardedComponent mask vector coordinate))
        (λ coordinate →
          covector coordinate
            * Projector.physicalCoordinateProject mask vector coordinate
          + covector coordinate
            * projectorDiscardedComponent mask vector coordinate)
        (λ coordinate → ℚRing.solve-∀
          (covector coordinate)
          (Projector.physicalCoordinateProject mask vector coordinate)
          (projectorDiscardedComponent mask vector coordinate)))
      (Sums.sumRationalAdd
        Physical.physicalSU2Coordinates4
        (λ coordinate →
          covector coordinate
            * Projector.physicalCoordinateProject mask vector coordinate)
        (λ coordinate →
          covector coordinate
            * projectorDiscardedComponent mask vector coordinate)))

projectedFirstVariationIsRawMinusDiscarded :
  ∀ covector mask vector →
  firstVariationFromCovector covector
    (Projector.physicalCoordinateProject mask vector)
  ≡ firstVariationFromCovector covector vector
    - firstVariationFromCovector covector
      (projectorDiscardedComponent mask vector)
projectedFirstVariationIsRawMinusDiscarded covector mask vector =
  let
    split = firstVariationRawSplitsProjectedDiscarded
      covector mask vector
  in
  trans
    (sym (ℚRing.solve-∀
      (firstVariationFromCovector covector vector)
      (firstVariationFromCovector covector
        (Projector.physicalCoordinateProject mask vector))
      (firstVariationFromCovector covector
        (projectorDiscardedComponent mask vector))))
    (cong
      (λ selected →
        selected
        - firstVariationFromCovector covector
          (projectorDiscardedComponent mask vector))
      split)

record ProjectionSpilloverData
    (background : Plaquette.RationalSU2Background4)
    (field : Physical.PhysicalSU2BondField4)
    (plaquette : Plaquette.Plaquette4) : Set₁ where
  field
    physicalHodgeMask : Projector.PhysicalCoordinateMask
    firstVariationCovector : PhysicalVector

    rawLocalizationSpillover : ℚ
    rawSpillCoefficient : ℚ
    projectorDefectCoefficient : ℚ

    rawExtractorIdentity :
      firstVariationFromCovector firstVariationCovector
        (Boundary.rawPlaquetteSingletonExtractor field plaquette)
      ≡ Partition.physicalPlaquetteWilsonLinearPart
          background field plaquette
        + rawLocalizationSpillover

    rawLocalizationSpilloverUpper :
      rawLocalizationSpillover
      ≤ rawSpillCoefficient
        * Wilson.plaquetteCrossCharge field plaquette

    projectorDefectPairingUpper :
      - firstVariationFromCovector firstVariationCovector
          (projectorDiscardedComponent physicalHodgeMask
            (Boundary.rawPlaquetteSingletonExtractor field plaquette))
      ≤ projectorDefectCoefficient
        * Wilson.plaquetteCrossCharge field plaquette

    coefficientsExhaustSingletonBudget :
      rawSpillCoefficient + projectorDefectCoefficient
      ≡ Selector.remainingSingletonCoefficient

open ProjectionSpilloverData public

projectedExtractionSpillover :
  ∀ {background field plaquette} →
  ProjectionSpilloverData background field plaquette → ℚ
projectedExtractionSpillover data =
  rawLocalizationSpillover data
  - firstVariationFromCovector
      (firstVariationCovector data)
      (projectorDiscardedComponent
        (physicalHodgeMask data)
        (Boundary.rawPlaquetteSingletonExtractor _ _))

projectedExtractorIdentity :
  ∀ {background field plaquette}
    (data : ProjectionSpilloverData background field plaquette) →
  firstVariationFromCovector (firstVariationCovector data)
    (Projector.physicalCoordinateProject
      (physicalHodgeMask data)
      (Boundary.rawPlaquetteSingletonExtractor field plaquette))
  ≡ Partition.physicalPlaquetteWilsonLinearPart
      background field plaquette
    + projectedExtractionSpillover data
projectedExtractorIdentity {background} {field} {plaquette} data =
  trans
    (projectedFirstVariationIsRawMinusDiscarded
      (firstVariationCovector data)
      (physicalHodgeMask data)
      (Boundary.rawPlaquetteSingletonExtractor field plaquette))
    (trans
      (cong
        (λ selected →
          selected
          - firstVariationFromCovector
              (firstVariationCovector data)
              (projectorDiscardedComponent
                (physicalHodgeMask data)
                (Boundary.rawPlaquetteSingletonExtractor field plaquette)))
        (rawExtractorIdentity data))
      (ℚRing.solve-∀
        (Partition.physicalPlaquetteWilsonLinearPart
          background field plaquette)
        (rawLocalizationSpillover data)
        (firstVariationFromCovector
          (firstVariationCovector data)
          (projectorDiscardedComponent
            (physicalHodgeMask data)
            (Boundary.rawPlaquetteSingletonExtractor field plaquette))))))

projectedExtractionSpilloverUpper :
  ∀ {background field plaquette}
    (data : ProjectionSpilloverData background field plaquette) →
  projectedExtractionSpillover data
  ≤ Selector.remainingSingletonCoefficient
      * Wilson.plaquetteCrossCharge field plaquette
projectedExtractionSpilloverUpper {field = field} {plaquette = plaquette} data =
  let
    rawBound = rawLocalizationSpilloverUpper data
    defectBound = projectorDefectPairingUpper data
    added = ℚP.+-mono-≤ rawBound defectBound
    charge = Wilson.plaquetteCrossCharge field plaquette
  in
  subst
    (λ left →
      projectedExtractionSpillover data
      ≤ left * charge)
    (coefficientsExhaustSingletonBudget data)
    (subst
      (λ right → projectedExtractionSpillover data ≤ right)
      (ℚRing.solve-∀
        (rawSpillCoefficient data)
        (projectorDefectCoefficient data)
        charge)
      (subst
        (λ left → left
          ≤ rawSpillCoefficient data * charge
            + projectorDefectCoefficient data * charge)
        (ℚRing.solve-∀
          (rawLocalizationSpillover data)
          (firstVariationFromCovector
            (firstVariationCovector data)
            (projectorDiscardedComponent
              (physicalHodgeMask data)
              (Boundary.rawPlaquetteSingletonExtractor field plaquette))))
        added))

projectionSpilloverDecompositionLevel : ProofLevel
projectionSpilloverDecompositionLevel = machineChecked

projectionSpilloverBudgetCompositionLevel : ProofLevel
projectionSpilloverBudgetCompositionLevel = machineChecked
