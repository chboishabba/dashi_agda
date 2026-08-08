module DASHI.Physics.YangMills.BalabanSelectedRawExtractorConstraintDefectExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- DASHI CONTRIBUTION
--
-- Compute the constraint defect of the literal four-bond plaquette extractor
-- before materialising the global KKT repair:
--
--   delta_(p,h) = L w_(p,h).
--
-- The defect is represented by the finite matrix L P_boundary(p), and the
-- Round-38 multiplier identity specializes exactly to
--
--   dS((I-P)w_(p,h)) = <lambda, delta_(p,h)>.
--
-- A row-locality certificate then proves that rows whose constraint stencil
-- misses the four boundary bonds contribute exactly zero.  The estimate is
-- therefore reduced from 3072 state coordinates to the finite multiplier
-- collar selected by the actual constraint matrix.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; -_; _≤_)
open import Relation.Binary.PropositionalEquality using
  (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateProjectorExact as Projector
import DASHI.Physics.YangMills.BalabanP33PlaquetteBoundaryProjectorExact as Boundary
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33LiteralResidualKernelNumericalCalibrationExact as Calibration
import DASHI.Physics.YangMills.BalabanP33PhysicalCombesThomasEntryDecayExact as Entry
import DASHI.Physics.YangMills.BalabanSelectedVariationKKTMultiplierExact as Stationary

boundaryProjectorMatrixApplyExact :
  ∀ plaquette vector coordinate →
  Rect.applyRectangular
    KKT.physicalStateCarrier
    (Boundary.plaquetteBoundaryProjectorMatrix plaquette)
    vector coordinate
  ≡ Boundary.plaquetteBoundaryProject plaquette vector coordinate
boundaryProjectorMatrixApplyExact plaquette vector coordinate =
  let
    mask = Boundary.plaquetteBoundaryMask plaquette

    projectedIdentity =
      Projector.projectedPhysicalMatrixApplyExact
        mask Calibration.identityEntry vector coordinate

    identityAfterProjection :
      Coordinates.physicalMatrixApply Calibration.identityEntry
        (Projector.physicalCoordinateProject mask vector)
        coordinate
      ≡ Projector.physicalCoordinateProject mask vector coordinate
    identityAfterProjection =
      Entry.physicalIdentityApplyExact
        (Projector.physicalCoordinateProject mask vector)
        coordinate
  in
  trans projectedIdentity
    (trans
      (cong
        (Projector.maskSelect (mask coordinate))
        identityAfterProjection)
      (Projector.physicalConstraintProjectorIdempotent
        mask vector coordinate))

rawExtractorConstraintDefectMatrix :
  ∀ {Multiplier} →
  KKT.FiniteKKTProjectorData Multiplier →
  Physical.Plaquette4 →
  Rect.RectangularMatrix Multiplier KKT.State
rawExtractorConstraintDefectMatrix data plaquette =
  Rect.composeRectangular
    KKT.physicalStateCarrier
    (KKT.constraintMatrix data)
    (Boundary.plaquetteBoundaryProjectorMatrix plaquette)

rawExtractorConstraintDefect :
  ∀ {Multiplier} →
  KKT.FiniteKKTProjectorData Multiplier →
  Coordinates.PhysicalSU2BondField4 →
  Physical.Plaquette4 →
  Multiplier → ℚ
rawExtractorConstraintDefect data field plaquette =
  KKT.constraintApply data
    (Boundary.rawPlaquetteSingletonExtractor field plaquette)

rawExtractorConstraintDefectMatrixExact :
  ∀ {Multiplier}
    (data : KKT.FiniteKKTProjectorData Multiplier)
    field plaquette row →
  Rect.applyRectangular
    KKT.physicalStateCarrier
    (rawExtractorConstraintDefectMatrix data plaquette)
    (Coordinates.encodePhysicalSU2 field)
    row
  ≡ rawExtractorConstraintDefect data field plaquette row
rawExtractorConstraintDefectMatrixExact
    data field plaquette row =
  trans
    (Rect.applyComposeRectangularExact
      KKT.physicalStateCarrier
      KKT.physicalStateCarrier
      (KKT.constraintMatrix data)
      (Boundary.plaquetteBoundaryProjectorMatrix plaquette)
      (Coordinates.encodePhysicalSU2 field)
      row)
    (Rect.applyRectangularVectorCong
      KKT.physicalStateCarrier
      (KKT.constraintMatrix data)
      (boundaryProjectorMatrixApplyExact
        plaquette (Coordinates.encodePhysicalSU2 field))
      row)

record ConstraintRowMissesBoundary
    {Multiplier : Set}
    (data : KKT.FiniteKKTProjectorData Multiplier)
    (plaquette : Physical.Plaquette4)
    (row : Multiplier) : Set where
  field
    localizedRowZero : ∀ coordinate →
      rawExtractorConstraintDefectMatrix data plaquette
        row coordinate
      ≡ 0ℚ

open ConstraintRowMissesBoundary public

missedConstraintRowDefectZero :
  ∀ {Multiplier}
    (data : KKT.FiniteKKTProjectorData Multiplier)
    field plaquette row →
  ConstraintRowMissesBoundary data plaquette row →
  rawExtractorConstraintDefect data field plaquette row ≡ 0ℚ
missedConstraintRowDefectZero data field plaquette row missed =
  trans
    (sym
      (rawExtractorConstraintDefectMatrixExact
        data field plaquette row))
    (trans
      (Sums.sumRationalCong
        (Matrix.coordinates KKT.physicalStateCarrier)
        (λ coordinate →
          rawExtractorConstraintDefectMatrix data plaquette
            row coordinate
          * Coordinates.encodePhysicalSU2 field coordinate)
        (λ coordinate →
          0ℚ * Coordinates.encodePhysicalSU2 field coordinate)
        (λ coordinate →
          cong
            (_* Coordinates.encodePhysicalSU2 field coordinate)
            (localizedRowZero missed coordinate)))
      (trans
        (Sums.sumRationalCong
          (Matrix.coordinates KKT.physicalStateCarrier)
          (λ coordinate →
            0ℚ * Coordinates.encodePhysicalSU2 field coordinate)
          (λ _ → 0ℚ)
          (λ coordinate → refl))
        (Fubini.sumRationalZero
          (Matrix.coordinates KKT.physicalStateCarrier))))

rawExtractorProjectorDefectPairingExact :
  ∀ {Multiplier}
    (data : Stationary.SelectedKKTStationaryData Multiplier)
    field plaquette →
  Stationary.firstVariation data
    (KKT.selectedConstraintRepair
      (Stationary.projectorData data)
      (Boundary.rawPlaquetteSingletonExtractor field plaquette))
  ≡ KKT.multiplierDot
      (Stationary.projectorData data)
      (Stationary.kktMultiplier data)
      (rawExtractorConstraintDefect
        (Stationary.projectorData data)
        field plaquette)
rawExtractorProjectorDefectPairingExact data field plaquette =
  Stationary.projectorDefectFirstVariationMultiplierIdentity
    data
    (Boundary.rawPlaquetteSingletonExtractor field plaquette)

rawExtractorDefectUpperReducesToMultiplier :
  ∀ {Multiplier}
    (data : Stationary.SelectedKKTStationaryData Multiplier)
    field plaquette bound →
  - KKT.multiplierDot
      (Stationary.projectorData data)
      (Stationary.kktMultiplier data)
      (rawExtractorConstraintDefect
        (Stationary.projectorData data)
        field plaquette)
    ≤ bound →
  - Stationary.firstVariation data
      (KKT.selectedConstraintRepair
        (Stationary.projectorData data)
        (Boundary.rawPlaquetteSingletonExtractor field plaquette))
    ≤ bound
rawExtractorDefectUpperReducesToMultiplier data field plaquette =
  Stationary.projectorDefectUpperReducesToMultiplier
    data
    (Boundary.rawPlaquetteSingletonExtractor field plaquette)

rawExtractorConstraintDefectMatrixLevel : ProofLevel
rawExtractorConstraintDefectMatrixLevel = machineChecked

rawExtractorKKTDefectPairingLevel : ProofLevel
rawExtractorKKTDefectPairingLevel = machineChecked

selectedConstraintStencilLocalityProducerLevel : ProofLevel
selectedConstraintStencilLocalityProducerLevel = conditional
