module DASHI.Physics.YangMills.BalabanPlaquetteBoundaryStateNormChargeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309. DOI: 10.1007/BF01229381.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Compute, on the literal 3072-coordinate SU(2) carrier, the norm of the
-- four-bond plaquette projector.  Pairwise distinctness of the four positive
-- bond cells plus exact finite Kronecker selection gives
--
--   ||P_p h||^2 = q_p(h),
--
-- where q_p is the repository's literal four-link diagonal Wilson charge.
-- The already-proved twelve-ordered-pair incidence identity is
--
--   C_p(h) = 3 q_p(h).
--
-- The defect degree-one Möbius state is exactly P_p h, so the physical G2
-- defect norm is not an analytic producer at all:
--
--   ||w_1||^2 = (1/3) C_p(h).
--
-- No pseudoinverse, row bound, LBB constant, or background stabilizer enters.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (pair; Empty; _≢_; yes; no)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33LiteralBondCellIncidenceExact as Cell
import DASHI.Physics.YangMills.BalabanP33LiteralResidualKernelNumericalCalibrationExact as Calibration
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis
import DASHI.Physics.YangMills.BalabanP33PlaquetteBoundaryProjectorExact as Boundary
import DASHI.Physics.YangMills.BalabanPlaquetteBoundaryCellsPairwiseDistinctExact as Distinct
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonIncidenceExact as Incidence
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeFirstExact as Gauge
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeJointExact as Degree
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintAtomsFromSubsetExact as Canonical
import DASHI.Physics.YangMills.BalabanCanonicalGreenDegreeStatePreimageExact as Preimage
import DASHI.Physics.YangMills.BalabanCanonicalGreenStateNormReductionExact as StateNorm
import DASHI.Physics.YangMills.BalabanPlaquetteSubsetMobiusDegreeOneCollapseExact as Collapse

emptyElim : ∀ {A : Set} → Empty → A
emptyElim ()

sq : ℚ → ℚ
sq value = value * value

kroneckerEqual : ∀ {left right : Cell.BondCell4} →
  left ≡ right →
  Basis.kronecker Calibration.bondCellDecidableEquality left right ≡ 1ℚ
kroneckerEqual refl
  with Calibration.bondCellDecidableEquality _ _
... | yes _ = refl
... | no notEqual = emptyElim (notEqual refl)

kroneckerNotEqual : ∀ {left right : Cell.BondCell4} →
  left ≢ right →
  Basis.kronecker Calibration.bondCellDecidableEquality left right ≡ 0ℚ
kroneckerNotEqual notEqual
  with Calibration.bondCellDecidableEquality _ _
... | yes equality = emptyElim (notEqual equality)
... | no _ = refl

boundaryIndicator :
  Boundary.Physical.Plaquette4 → Cell.BondCell4 → ℚ
boundaryIndicator plaquette cell =
  Basis.kronecker Calibration.bondCellDecidableEquality
    cell (Boundary.boundaryCell0 plaquette)
  + Basis.kronecker Calibration.bondCellDecidableEquality
    cell (Boundary.boundaryCell1 plaquette)
  + Basis.kronecker Calibration.bondCellDecidableEquality
    cell (Boundary.boundaryCell2 plaquette)
  + Basis.kronecker Calibration.bondCellDecidableEquality
    cell (Boundary.boundaryCell3 plaquette)

indicatorAt0 : ∀ plaquette cell →
  cell ≡ Boundary.boundaryCell0 plaquette →
  cell ≢ Boundary.boundaryCell1 plaquette →
  cell ≢ Boundary.boundaryCell2 plaquette →
  cell ≢ Boundary.boundaryCell3 plaquette →
  boundaryIndicator plaquette cell ≡ 1ℚ
indicatorAt0 plaquette cell eq0 ne1 ne2 ne3
  rewrite kroneckerEqual eq0
        | kroneckerNotEqual ne1
        | kroneckerNotEqual ne2
        | kroneckerNotEqual ne3 = ℚRing.solve []

indicatorAt1 : ∀ plaquette cell →
  cell ≢ Boundary.boundaryCell0 plaquette →
  cell ≡ Boundary.boundaryCell1 plaquette →
  cell ≢ Boundary.boundaryCell2 plaquette →
  cell ≢ Boundary.boundaryCell3 plaquette →
  boundaryIndicator plaquette cell ≡ 1ℚ
indicatorAt1 plaquette cell ne0 eq1 ne2 ne3
  rewrite kroneckerNotEqual ne0
        | kroneckerEqual eq1
        | kroneckerNotEqual ne2
        | kroneckerNotEqual ne3 = ℚRing.solve []

indicatorAt2 : ∀ plaquette cell →
  cell ≢ Boundary.boundaryCell0 plaquette →
  cell ≢ Boundary.boundaryCell1 plaquette →
  cell ≡ Boundary.boundaryCell2 plaquette →
  cell ≢ Boundary.boundaryCell3 plaquette →
  boundaryIndicator plaquette cell ≡ 1ℚ
indicatorAt2 plaquette cell ne0 ne1 eq2 ne3
  rewrite kroneckerNotEqual ne0
        | kroneckerNotEqual ne1
        | kroneckerEqual eq2
        | kroneckerNotEqual ne3 = ℚRing.solve []

indicatorAt3 : ∀ plaquette cell →
  cell ≢ Boundary.boundaryCell0 plaquette →
  cell ≢ Boundary.boundaryCell1 plaquette →
  cell ≢ Boundary.boundaryCell2 plaquette →
  cell ≡ Boundary.boundaryCell3 plaquette →
  boundaryIndicator plaquette cell ≡ 1ℚ
indicatorAt3 plaquette cell ne0 ne1 ne2 eq3
  rewrite kroneckerNotEqual ne0
        | kroneckerNotEqual ne1
        | kroneckerNotEqual ne2
        | kroneckerEqual eq3 = ℚRing.solve []

indicatorOutside : ∀ plaquette cell →
  cell ≢ Boundary.boundaryCell0 plaquette →
  cell ≢ Boundary.boundaryCell1 plaquette →
  cell ≢ Boundary.boundaryCell2 plaquette →
  cell ≢ Boundary.boundaryCell3 plaquette →
  boundaryIndicator plaquette cell ≡ 0ℚ
indicatorOutside plaquette cell ne0 ne1 ne2 ne3
  rewrite kroneckerNotEqual ne0
        | kroneckerNotEqual ne1
        | kroneckerNotEqual ne2
        | kroneckerNotEqual ne3 = ℚRing.solve []

bondCellEqualFalse : ∀ {left right} →
  left ≢ right → Boundary.bondCellEqual left right ≡ false
bondCellEqualFalse {left} {right} notEqual
  with Calibration.bondCellDecidableEquality left right
... | yes equality = emptyElim (notEqual equality)
... | no _ = refl

boundaryMaskOutside : ∀ plaquette coordinate →
  Boundary.physicalCoordinateCell coordinate ≢ Boundary.boundaryCell0 plaquette →
  Boundary.physicalCoordinateCell coordinate ≢ Boundary.boundaryCell1 plaquette →
  Boundary.physicalCoordinateCell coordinate ≢ Boundary.boundaryCell2 plaquette →
  Boundary.physicalCoordinateCell coordinate ≢ Boundary.boundaryCell3 plaquette →
  Boundary.plaquetteBoundaryMask plaquette coordinate ≡ false
boundaryMaskOutside plaquette coordinate ne0 ne1 ne2 ne3
  rewrite bondCellEqualFalse ne0
        | bondCellEqualFalse ne1
        | bondCellEqualFalse ne2
        | bondCellEqualFalse ne3 = refl

projectedSquareIndicatorExact :
  ∀ plaquette vector coordinate →
  Boundary.plaquetteBoundaryProject plaquette vector coordinate
    * Boundary.plaquetteBoundaryProject plaquette vector coordinate
  ≡ boundaryIndicator plaquette (Boundary.physicalCoordinateCell coordinate)
      * sq (vector coordinate)
projectedSquareIndicatorExact plaquette vector coordinate
  with Calibration.bondCellDecidableEquality
        (Boundary.physicalCoordinateCell coordinate)
        (Boundary.boundaryCell0 plaquette)
     | Calibration.bondCellDecidableEquality
        (Boundary.physicalCoordinateCell coordinate)
        (Boundary.boundaryCell1 plaquette)
     | Calibration.bondCellDecidableEquality
        (Boundary.physicalCoordinateCell coordinate)
        (Boundary.boundaryCell2 plaquette)
     | Calibration.bondCellDecidableEquality
        (Boundary.physicalCoordinateCell coordinate)
        (Boundary.boundaryCell3 plaquette)
... | yes eq0 | yes eq1 | d2 | d3 =
  emptyElim (Distinct.boundaryCell0Not1 plaquette (trans (sym eq0) eq1))
... | yes eq0 | no ne1 | yes eq2 | d3 =
  emptyElim (Distinct.boundaryCell0Not2 plaquette (trans (sym eq0) eq2))
... | yes eq0 | no ne1 | no ne2 | yes eq3 =
  emptyElim (Distinct.boundaryCell0Not3 plaquette (trans (sym eq0) eq3))
... | yes eq0 | no ne1 | no ne2 | no ne3
  rewrite Boundary.plaquetteBoundaryMaskAt0 plaquette coordinate eq0
        | indicatorAt0 plaquette (Boundary.physicalCoordinateCell coordinate)
            eq0 ne1 ne2 ne3 =
  ℚRing.solve-∀ (vector coordinate)
... | no ne0 | yes eq1 | yes eq2 | d3 =
  emptyElim (Distinct.boundaryCell1Not2 plaquette (trans (sym eq1) eq2))
... | no ne0 | yes eq1 | no ne2 | yes eq3 =
  emptyElim (Distinct.boundaryCell1Not3 plaquette (trans (sym eq1) eq3))
... | no ne0 | yes eq1 | no ne2 | no ne3
  rewrite Boundary.plaquetteBoundaryMaskAt1 plaquette coordinate eq1
        | indicatorAt1 plaquette (Boundary.physicalCoordinateCell coordinate)
            ne0 eq1 ne2 ne3 =
  ℚRing.solve-∀ (vector coordinate)
... | no ne0 | no ne1 | yes eq2 | yes eq3 =
  emptyElim (Distinct.boundaryCell2Not3 plaquette (trans (sym eq2) eq3))
... | no ne0 | no ne1 | yes eq2 | no ne3
  rewrite Boundary.plaquetteBoundaryMaskAt2 plaquette coordinate eq2
        | indicatorAt2 plaquette (Boundary.physicalCoordinateCell coordinate)
            ne0 ne1 eq2 ne3 =
  ℚRing.solve-∀ (vector coordinate)
... | no ne0 | no ne1 | no ne2 | yes eq3
  rewrite Boundary.plaquetteBoundaryMaskAt3 plaquette coordinate eq3
        | indicatorAt3 plaquette (Boundary.physicalCoordinateCell coordinate)
            ne0 ne1 ne2 eq3 =
  ℚRing.solve-∀ (vector coordinate)
... | no ne0 | no ne1 | no ne2 | no ne3
  rewrite boundaryMaskOutside plaquette coordinate ne0 ne1 ne2 ne3
        | indicatorOutside plaquette (Boundary.physicalCoordinateCell coordinate)
            ne0 ne1 ne2 ne3 =
  ℚRing.solve-∀ (vector coordinate)

selectedCellSquareSum :
  Physical.PhysicalSU2BondField4 → Cell.BondCell4 → ℚ
selectedCellSquareSum field target =
  Sums.sumRational Physical.physicalSU2Coordinates4
    (λ coordinate →
      Basis.kronecker Calibration.bondCellDecidableEquality
        (Boundary.physicalCoordinateCell coordinate) target
      * sq (Physical.encodePhysicalSU2 field coordinate))

bondCellPhysicalCharge :
  Physical.PhysicalSU2BondField4 → Cell.BondCell4 → ℚ
bondCellPhysicalCharge field cell =
  Sums.sumRational Physical.lieCoordinates3
    (λ coordinate → sq (Cell.bondCellValue (field coordinate) cell))

selectedCellSquareSumExact : ∀ field target →
  selectedCellSquareSum field target ≡ bondCellPhysicalCharge field target
selectedCellSquareSumExact field target =
  trans
    (Fubini.sumCartesian Physical.lieCoordinates3 Cell.bondCells4
      (λ physicalCoordinate →
        Basis.kronecker Calibration.bondCellDecidableEquality
          (Boundary.physicalCoordinateCell physicalCoordinate) target
        * sq (Physical.encodePhysicalSU2 field physicalCoordinate)))
    (Sums.sumRationalCong Physical.lieCoordinates3 _ _
      (λ coordinate →
        trans
          (Sums.sumRationalCong Cell.bondCells4 _ _
            (λ cell → ℚRing.solve-∀
              (Cell.bondCellValue (field coordinate) cell)
              (Basis.kronecker Calibration.bondCellDecidableEquality cell target)))
          (Basis.selectorExact Basis.bondCellFiniteSelector
            (λ cell → sq (Cell.bondCellValue (field coordinate) cell)) target)))

bondCellPhysicalChargeIsInsertionCharge : ∀ field axis site →
  bondCellPhysicalCharge field (pair axis site)
  ≡ Incidence.linkInsertionCharge field axis site
bondCellPhysicalChargeIsInsertionCharge field axis site =
  ℚRing.solve-∀
    (field Physical.coordinateX (pair site axis))
    (field Physical.coordinateY (pair site axis))
    (field Physical.coordinateZ (pair site axis))

sumIndicatorSquareExact : ∀ plaquette field →
  Sums.sumRational Physical.physicalSU2Coordinates4
    (λ coordinate →
      boundaryIndicator plaquette (Boundary.physicalCoordinateCell coordinate)
      * sq (Physical.encodePhysicalSU2 field coordinate))
  ≡ bondCellPhysicalCharge field (Boundary.boundaryCell0 plaquette)
    + bondCellPhysicalCharge field (Boundary.boundaryCell1 plaquette)
    + bondCellPhysicalCharge field (Boundary.boundaryCell2 plaquette)
    + bondCellPhysicalCharge field (Boundary.boundaryCell3 plaquette)
sumIndicatorSquareExact plaquette field =
  let
    coordinates = Physical.physicalSU2Coordinates4
    term : Cell.BondCell4 → Physical.PhysicalSU2Coordinate4 → ℚ
    term target coordinate =
      Basis.kronecker Calibration.bondCellDecidableEquality
        (Boundary.physicalCoordinateCell coordinate) target
      * sq (Physical.encodePhysicalSU2 field coordinate)

    expand :
      Sums.sumRational coordinates
        (λ coordinate →
          boundaryIndicator plaquette (Boundary.physicalCoordinateCell coordinate)
          * sq (Physical.encodePhysicalSU2 field coordinate))
      ≡ Sums.sumRational coordinates
          (λ coordinate → term (Boundary.boundaryCell0 plaquette) coordinate
            + term (Boundary.boundaryCell1 plaquette) coordinate
            + term (Boundary.boundaryCell2 plaquette) coordinate
            + term (Boundary.boundaryCell3 plaquette) coordinate)
    expand = Sums.sumRationalCong coordinates _ _
      (λ coordinate → ℚRing.solve-∀
        (Basis.kronecker Calibration.bondCellDecidableEquality
          (Boundary.physicalCoordinateCell coordinate)
          (Boundary.boundaryCell0 plaquette))
        (Basis.kronecker Calibration.bondCellDecidableEquality
          (Boundary.physicalCoordinateCell coordinate)
          (Boundary.boundaryCell1 plaquette))
        (Basis.kronecker Calibration.bondCellDecidableEquality
          (Boundary.physicalCoordinateCell coordinate)
          (Boundary.boundaryCell2 plaquette))
        (Basis.kronecker Calibration.bondCellDecidableEquality
          (Boundary.physicalCoordinateCell coordinate)
          (Boundary.boundaryCell3 plaquette))
        (sq (Physical.encodePhysicalSU2 field coordinate)))

    split0 = Fubini.sumRationalAdd coordinates
      (λ coordinate → term (Boundary.boundaryCell0 plaquette) coordinate)
      (λ coordinate → term (Boundary.boundaryCell1 plaquette) coordinate
        + term (Boundary.boundaryCell2 plaquette) coordinate
        + term (Boundary.boundaryCell3 plaquette) coordinate)
    split1 = Fubini.sumRationalAdd coordinates
      (λ coordinate → term (Boundary.boundaryCell1 plaquette) coordinate)
      (λ coordinate → term (Boundary.boundaryCell2 plaquette) coordinate
        + term (Boundary.boundaryCell3 plaquette) coordinate)
    split2 = Fubini.sumRationalAdd coordinates
      (λ coordinate → term (Boundary.boundaryCell2 plaquette) coordinate)
      (λ coordinate → term (Boundary.boundaryCell3 plaquette) coordinate)
  in
  trans expand
    (trans split0
      (cong
        (selectedCellSquareSum field (Boundary.boundaryCell0 plaquette) +_)
        (trans split1
          (cong
            (selectedCellSquareSum field (Boundary.boundaryCell1 plaquette) +_)
            split2))))
  |> λ split →
    trans split
      (cong₂ _+_
        (selectedCellSquareSumExact field (Boundary.boundaryCell0 plaquette))
        (cong₂ _+_
          (selectedCellSquareSumExact field (Boundary.boundaryCell1 plaquette))
          (cong₂ _+_
            (selectedCellSquareSumExact field (Boundary.boundaryCell2 plaquette))
            (selectedCellSquareSumExact field (Boundary.boundaryCell3 plaquette)))))
  where
  infixl 0 _|>_
  _|>_ : ∀ {A B : Set} → A → (A → B) → B
  value |> function = function value

boundaryCellChargesArePlaquetteDiagonal : ∀ field plaquette →
  bondCellPhysicalCharge field (Boundary.boundaryCell0 plaquette)
    + bondCellPhysicalCharge field (Boundary.boundaryCell1 plaquette)
    + bondCellPhysicalCharge field (Boundary.boundaryCell2 plaquette)
    + bondCellPhysicalCharge field (Boundary.boundaryCell3 plaquette)
  ≡ Incidence.plaquetteDiagonalCharge field
      (Boundary.Physical.pairLeft (Boundary.Physical.plaquetteAxes plaquette))
      (Boundary.Physical.pairRight (Boundary.Physical.plaquetteAxes plaquette))
      (Boundary.Physical.plaquetteSite plaquette)
boundaryCellChargesArePlaquetteDiagonal field (pair site axes)
  rewrite bondCellPhysicalChargeIsInsertionCharge field
      (Boundary.Physical.pairLeft axes) site
        | bondCellPhysicalChargeIsInsertionCharge field
      (Boundary.Physical.pairRight axes)
      (Boundary.Hodge4.shiftForward (Boundary.Physical.pairLeft axes) site)
        | bondCellPhysicalChargeIsInsertionCharge field
      (Boundary.Physical.pairLeft axes)
      (Boundary.Hodge4.shiftForward (Boundary.Physical.pairRight axes) site)
        | bondCellPhysicalChargeIsInsertionCharge field
      (Boundary.Physical.pairRight axes) site =
  sym (Incidence.plaquetteDiagonalChargeExpanded field
    (Boundary.Physical.pairLeft axes) (Boundary.Physical.pairRight axes) site)

plaquetteBoundaryProjectNormSqIsDiagonalCharge : ∀ field plaquette →
  Rect.finiteNormSq KKT.physicalStateCarrier
    (Boundary.rawPlaquetteSingletonExtractor field plaquette)
  ≡ Incidence.plaquetteDiagonalCharge field
      (Boundary.Physical.pairLeft (Boundary.Physical.plaquetteAxes plaquette))
      (Boundary.Physical.pairRight (Boundary.Physical.plaquetteAxes plaquette))
      (Boundary.Physical.plaquetteSite plaquette)
plaquetteBoundaryProjectNormSqIsDiagonalCharge field plaquette =
  trans
    (Sums.sumRationalCong Physical.physicalSU2Coordinates4 _ _
      (projectedSquareIndicatorExact plaquette
        (Physical.encodePhysicalSU2 field)))
    (trans
      (sumIndicatorSquareExact plaquette field)
      (boundaryCellChargesArePlaquetteDiagonal field plaquette))

-- The user-facing Wilson charge has the same plaquette packaging.
plaquetteBoundaryProjectNormSqIsOneThirdCrossCharge : ∀ field plaquette →
  (+ 3 / 1)
    * Rect.finiteNormSq KKT.physicalStateCarrier
        (Boundary.rawPlaquetteSingletonExtractor field plaquette)
  ≡ Incidence.plaquetteCrossCharge field
      (Boundary.Physical.pairLeft (Boundary.Physical.plaquetteAxes plaquette))
      (Boundary.Physical.pairRight (Boundary.Physical.plaquetteAxes plaquette))
      (Boundary.Physical.plaquetteSite plaquette)
plaquetteBoundaryProjectNormSqIsOneThirdCrossCharge field plaquette =
  trans
    (cong ((+ 3 / 1) *_)
      (plaquetteBoundaryProjectNormSqIsDiagonalCharge field plaquette))
    (sym (Incidence.plaquetteCrossChargeIsThreeDiagonal field
      (Boundary.Physical.pairLeft (Boundary.Physical.plaquetteAxes plaquette))
      (Boundary.Physical.pairRight (Boundary.Physical.plaquetteAxes plaquette))
      (Boundary.Physical.plaquetteSite plaquette)))

-- Exact pointwise degree-one identification.
defectDegreeOneStateIsBoundaryProject :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette)
    coordinate →
  Preimage.defectDegreeState inputs Degree.degree1 coordinate
  ≡ Boundary.rawPlaquetteSingletonExtractor bondField plaquette coordinate
defectDegreeOneStateIsBoundaryProject
    {bondField = bondField} {plaquette = plaquette} inputs coordinate =
  Collapse.layer1IsBoundary
    (Physical.encodePhysicalSU2 bondField) plaquette coordinate

defectDegreeOneStateNormIsBoundaryNorm :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette) →
  StateNorm.defectStateNormSq inputs Degree.degree1
  ≡ Rect.finiteNormSq KKT.physicalStateCarrier
      (Boundary.rawPlaquetteSingletonExtractor bondField plaquette)
defectDegreeOneStateNormIsBoundaryNorm inputs =
  trans
    (Rect.finiteDotLeftPointwiseCong KKT.physicalStateCarrier
      (defectDegreeOneStateIsBoundaryProject inputs))
    (Rect.finiteDotRightPointwiseCong KKT.physicalStateCarrier
      (defectDegreeOneStateIsBoundaryProject inputs))

selectedG2DefectDegreeOneNormChargeExact :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette) →
  (+ 3 / 1) * StateNorm.defectStateNormSq inputs Degree.degree1
  ≡ Incidence.plaquetteCrossCharge bondField
      (Boundary.Physical.pairLeft (Boundary.Physical.plaquetteAxes plaquette))
      (Boundary.Physical.pairRight (Boundary.Physical.plaquetteAxes plaquette))
      (Boundary.Physical.plaquetteSite plaquette)
selectedG2DefectDegreeOneNormChargeExact
    {bondField = bondField} {plaquette = plaquette} inputs =
  trans
    (cong ((+ 3 / 1) *_)
      (defectDegreeOneStateNormIsBoundaryNorm inputs))
    (plaquetteBoundaryProjectNormSqIsOneThirdCrossCharge bondField plaquette)

plaquetteBoundaryStateNormChargeLevel : ProofLevel
plaquetteBoundaryStateNormChargeLevel = machineChecked

selectedG2DefectDegreeOneNormChargeBoundLevel : ProofLevel
selectedG2DefectDegreeOneNormChargeBoundLevel = machineChecked
