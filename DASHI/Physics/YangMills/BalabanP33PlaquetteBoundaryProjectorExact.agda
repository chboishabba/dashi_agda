module DASHI.Physics.YangMills.BalabanP33PlaquetteBoundaryProjectorExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Construct the literal plaquette-boundary localization projector on the
-- physical 3072-coordinate carrier.  For p=(x;mu,nu), the mask retains exactly
-- the four positive bonds occurring in
--
--   U_mu(x) U_nu(x+mu) U_mu(x+nu)^-1 U_nu(x)^-1
--
-- in all three su(2) coordinates.  The raw local extractor is the physical
-- perturbation restricted by this mask.  Idempotence, self-adjointness, image
-- locality and the constrained basis resolution are inherited as theorems from
-- the concrete coordinate projector, not stored as assumptions.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _*_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (Product; pair; Empty; yes; no)
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33LiteralBondCellIncidenceExact as Cell
import DASHI.Physics.YangMills.BalabanP33LiteralResidualKernelNumericalCalibrationExact as Calibration
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Hodge4
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateProjectorExact as Projector
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis

infixr 4 _or_

_or_ : Bool → Bool → Bool
false or right = right
true or right = true

emptyElim : ∀ {A : Set} → Empty → A
emptyElim ()

bondCellEqual : Cell.BondCell4 → Cell.BondCell4 → Bool
bondCellEqual left right
  with Calibration.bondCellDecidableEquality left right
... | yes _ = true
... | no _ = false

bondCellEqualRefl : ∀ cell →
  bondCellEqual cell cell ≡ true
bondCellEqualRefl cell
  with Calibration.bondCellDecidableEquality cell cell
... | yes _ = refl
... | no notEqual = emptyElim (notEqual refl)

boundaryCell0 : Physical.Plaquette4 → Cell.BondCell4
boundaryCell0 (pair site axes) =
  pair (Physical.pairLeft axes) site

boundaryCell1 : Physical.Plaquette4 → Cell.BondCell4
boundaryCell1 (pair site axes) =
  pair (Physical.pairRight axes)
    (Hodge4.shiftForward (Physical.pairLeft axes) site)

boundaryCell2 : Physical.Plaquette4 → Cell.BondCell4
boundaryCell2 (pair site axes) =
  pair (Physical.pairLeft axes)
    (Hodge4.shiftForward (Physical.pairRight axes) site)

boundaryCell3 : Physical.Plaquette4 → Cell.BondCell4
boundaryCell3 (pair site axes) =
  pair (Physical.pairRight axes) site

physicalCoordinateCell :
  Coordinates.PhysicalSU2Coordinate4 → Cell.BondCell4
physicalCoordinateCell (pair coordinate cell) = cell

plaquetteBoundaryMask :
  Physical.Plaquette4 → Projector.PhysicalCoordinateMask
plaquetteBoundaryMask plaquette coordinate =
  bondCellEqual (physicalCoordinateCell coordinate) (boundaryCell0 plaquette)
  or
  (bondCellEqual (physicalCoordinateCell coordinate) (boundaryCell1 plaquette)
  or
  (bondCellEqual (physicalCoordinateCell coordinate) (boundaryCell2 plaquette)
  or
   bondCellEqual (physicalCoordinateCell coordinate) (boundaryCell3 plaquette)))

plaquetteBoundaryMaskAt0 : ∀ plaquette coordinate →
  physicalCoordinateCell coordinate ≡ boundaryCell0 plaquette →
  plaquetteBoundaryMask plaquette coordinate ≡ true
plaquetteBoundaryMaskAt0 plaquette coordinate cellExact
  rewrite cellExact | bondCellEqualRefl (boundaryCell0 plaquette) = refl

plaquetteBoundaryMaskAt1 : ∀ plaquette coordinate →
  physicalCoordinateCell coordinate ≡ boundaryCell1 plaquette →
  plaquetteBoundaryMask plaquette coordinate ≡ true
plaquetteBoundaryMaskAt1 plaquette coordinate cellExact
  rewrite cellExact | bondCellEqualRefl (boundaryCell1 plaquette)
  with bondCellEqual (boundaryCell1 plaquette) (boundaryCell0 plaquette)
... | false = refl
... | true = refl

plaquetteBoundaryMaskAt2 : ∀ plaquette coordinate →
  physicalCoordinateCell coordinate ≡ boundaryCell2 plaquette →
  plaquetteBoundaryMask plaquette coordinate ≡ true
plaquetteBoundaryMaskAt2 plaquette coordinate cellExact
  rewrite cellExact | bondCellEqualRefl (boundaryCell2 plaquette)
  with bondCellEqual (boundaryCell2 plaquette) (boundaryCell0 plaquette)
     | bondCellEqual (boundaryCell2 plaquette) (boundaryCell1 plaquette)
... | false | false = refl
... | false | true = refl
... | true | false = refl
... | true | true = refl

plaquetteBoundaryMaskAt3 : ∀ plaquette coordinate →
  physicalCoordinateCell coordinate ≡ boundaryCell3 plaquette →
  plaquetteBoundaryMask plaquette coordinate ≡ true
plaquetteBoundaryMaskAt3 plaquette coordinate cellExact
  rewrite cellExact | bondCellEqualRefl (boundaryCell3 plaquette)
  with bondCellEqual (boundaryCell3 plaquette) (boundaryCell0 plaquette)
     | bondCellEqual (boundaryCell3 plaquette) (boundaryCell1 plaquette)
     | bondCellEqual (boundaryCell3 plaquette) (boundaryCell2 plaquette)
... | false | false | false = refl
... | false | false | true = refl
... | false | true | false = refl
... | false | true | true = refl
... | true | false | false = refl
... | true | false | true = refl
... | true | true | false = refl
... | true | true | true = refl

plaquetteBoundaryProject :
  Physical.Plaquette4 →
  Projector.PhysicalVector → Projector.PhysicalVector
plaquetteBoundaryProject plaquette =
  Projector.physicalCoordinateProject
    (plaquetteBoundaryMask plaquette)

plaquetteBoundaryProjectorMatrix :
  Physical.Plaquette4 → Projector.PhysicalMatrix
plaquetteBoundaryProjectorMatrix plaquette =
  Projector.maskProjectorMatrix (plaquetteBoundaryMask plaquette)

rawPlaquetteSingletonExtractor :
  Coordinates.PhysicalSU2BondField4 →
  Physical.Plaquette4 →
  Projector.PhysicalVector
rawPlaquetteSingletonExtractor field plaquette =
  plaquetteBoundaryProject plaquette
    (Coordinates.encodePhysicalSU2 field)

rawPlaquetteSingletonExtractorLocal :
  ∀ field plaquette →
  Projector.PhysicalConstraintProjectorImage
    (plaquetteBoundaryMask plaquette)
    (rawPlaquetteSingletonExtractor field plaquette)
rawPlaquetteSingletonExtractorLocal field plaquette =
  Projector.physicalCoordinateProjectLiesInImage
    (plaquetteBoundaryMask plaquette)
    (Coordinates.encodePhysicalSU2 field)

plaquetteBoundaryProjectorIdempotent :
  ∀ plaquette vector coordinate →
  plaquetteBoundaryProject plaquette
    (plaquetteBoundaryProject plaquette vector) coordinate
  ≡ plaquetteBoundaryProject plaquette vector coordinate
plaquetteBoundaryProjectorIdempotent plaquette =
  Projector.physicalConstraintProjectorIdempotent
    (plaquetteBoundaryMask plaquette)

plaquetteBoundaryProjectorSelfAdjoint :
  ∀ plaquette left right →
  Coordinates.physicalCoordinateDot left
    (plaquetteBoundaryProject plaquette right)
  ≡ Coordinates.physicalCoordinateDot
      (plaquetteBoundaryProject plaquette left) right
plaquetteBoundaryProjectorSelfAdjoint plaquette =
  Projector.physicalConstraintProjectorSelfAdjoint
    (plaquetteBoundaryMask plaquette)

plaquetteBoundaryResolutionOfIdentity :
  ∀ plaquette vector row →
  plaquetteBoundaryProject plaquette vector row
  ≡
  Sums.sumRational
    Coordinates.physicalSU2Coordinates4
    (λ column →
      plaquetteBoundaryProject plaquette
        (Basis.physicalBasis column)
        row
      * vector column)
plaquetteBoundaryResolutionOfIdentity plaquette =
  Projector.physicalConstrainedResolutionOfIdentity
    (plaquetteBoundaryMask plaquette)

plaquetteBoundaryProjectorLevel : ProofLevel
plaquetteBoundaryProjectorLevel = machineChecked

rawPlaquetteSingletonExtractorLocalLevel : ProofLevel
rawPlaquetteSingletonExtractorLocalLevel = machineChecked

plaquetteBoundaryResolutionLevel : ProofLevel
plaquetteBoundaryResolutionLevel = machineChecked
