module DASHI.Physics.YangMills.BalabanCMP109SU2AdCoordinateMassExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Construct the literal three-by-three matrix of ad_X(v)=X cross v on the
-- repository's {X,Y,Z} Lie-coordinate carrier.  The absolute column masses are
-- computed exactly:
--
--   col_X(A_X)=|x2|+|x1|,
--   col_Y(A_X)=|x2|+|x0|,
--   col_Z(A_X)=|x1|+|x0|.
--
-- Thus a coordinate cube |x_i|<=rho gives col(A_X)<=2 rho, and a coordinate
-- difference cube |x_i-y_i|<=delta gives
-- col(A_X-A_Y)<=2 delta.  These are the missing concrete C=2 rho and D=2
-- delta inputs for the ad-square and principal-log variation modules.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; -_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteRectangularSchurSquaredExact as RectSchur
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedJacobianExact as Jacobian
import DASHI.Physics.YangMills.BalabanCMP109FederbushComponentVariationExact as Variation

adMatrix : ℚ → ℚ → ℚ → Jacobian.Lie3Matrix
adMatrix x0 x1 x2 Physical.coordinateX Physical.coordinateX = 0ℚ
adMatrix x0 x1 x2 Physical.coordinateX Physical.coordinateY = - x2
adMatrix x0 x1 x2 Physical.coordinateX Physical.coordinateZ = x1
adMatrix x0 x1 x2 Physical.coordinateY Physical.coordinateX = x2
adMatrix x0 x1 x2 Physical.coordinateY Physical.coordinateY = 0ℚ
adMatrix x0 x1 x2 Physical.coordinateY Physical.coordinateZ = - x0
adMatrix x0 x1 x2 Physical.coordinateZ Physical.coordinateX = - x1
adMatrix x0 x1 x2 Physical.coordinateZ Physical.coordinateY = x0
adMatrix x0 x1 x2 Physical.coordinateZ Physical.coordinateZ = 0ℚ

adMatrixDifferenceExact : ∀ x0 x1 x2 y0 y1 y2 row column →
  Variation.matrixDifference
    (adMatrix x0 x1 x2) (adMatrix y0 y1 y2) row column
  ≡ adMatrix (x0 - y0) (x1 - y1) (x2 - y2) row column
adMatrixDifferenceExact x0 x1 x2 y0 y1 y2 Physical.coordinateX Physical.coordinateX =
  ℚRing.solve []
adMatrixDifferenceExact x0 x1 x2 y0 y1 y2 Physical.coordinateX Physical.coordinateY =
  ℚRing.solve-∀ x2 y2
adMatrixDifferenceExact x0 x1 x2 y0 y1 y2 Physical.coordinateX Physical.coordinateZ =
  ℚRing.solve-∀ x1 y1
adMatrixDifferenceExact x0 x1 x2 y0 y1 y2 Physical.coordinateY Physical.coordinateX =
  ℚRing.solve-∀ x2 y2
adMatrixDifferenceExact x0 x1 x2 y0 y1 y2 Physical.coordinateY Physical.coordinateY =
  ℚRing.solve []
adMatrixDifferenceExact x0 x1 x2 y0 y1 y2 Physical.coordinateY Physical.coordinateZ =
  ℚRing.solve-∀ x0 y0
adMatrixDifferenceExact x0 x1 x2 y0 y1 y2 Physical.coordinateZ Physical.coordinateX =
  ℚRing.solve-∀ x1 y1
adMatrixDifferenceExact x0 x1 x2 y0 y1 y2 Physical.coordinateZ Physical.coordinateY =
  ℚRing.solve-∀ x0 y0
adMatrixDifferenceExact x0 x1 x2 y0 y1 y2 Physical.coordinateZ Physical.coordinateZ =
  ℚRing.solve []

adColumnXExact : ∀ x0 x1 x2 →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    (adMatrix x0 x1 x2) Physical.coordinateX
  ≡ ∣ x2 ∣ + ∣ x1 ∣
adColumnXExact x0 x1 x2
  rewrite ℚP.∣-p∣≡∣p∣ x1 = ℚRing.solve-∀ ∣ x2 ∣ ∣ x1 ∣

adColumnYExact : ∀ x0 x1 x2 →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    (adMatrix x0 x1 x2) Physical.coordinateY
  ≡ ∣ x2 ∣ + ∣ x0 ∣
adColumnYExact x0 x1 x2
  rewrite ℚP.∣-p∣≡∣p∣ x2 = ℚRing.solve-∀ ∣ x2 ∣ ∣ x0 ∣

adColumnZExact : ∀ x0 x1 x2 →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    (adMatrix x0 x1 x2) Physical.coordinateZ
  ≡ ∣ x1 ∣ + ∣ x0 ∣
adColumnZExact x0 x1 x2
  rewrite ℚP.∣-p∣≡∣p∣ x0 = ℚRing.solve-∀ ∣ x1 ∣ ∣ x0 ∣

record CoordinateCube (x0 x1 x2 radius : ℚ) : Set where
  field
    x0Bound : ∣ x0 ∣ ≤ radius
    x1Bound : ∣ x1 ∣ ≤ radius
    x2Bound : ∣ x2 ∣ ≤ radius

open CoordinateCube public

adCoordinateCubeColumnBound :
  ∀ x0 x1 x2 radius →
  CoordinateCube x0 x1 x2 radius →
  ∀ column →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    (adMatrix x0 x1 x2) column
  ≤ radius + radius
adCoordinateCubeColumnBound x0 x1 x2 radius cube Physical.coordinateX =
  subst
    (λ lower → lower ≤ radius + radius)
    (sym (adColumnXExact x0 x1 x2))
    (ℚP.+-mono-≤ (x2Bound cube) (x1Bound cube))
adCoordinateCubeColumnBound x0 x1 x2 radius cube Physical.coordinateY =
  subst
    (λ lower → lower ≤ radius + radius)
    (sym (adColumnYExact x0 x1 x2))
    (ℚP.+-mono-≤ (x2Bound cube) (x0Bound cube))
adCoordinateCubeColumnBound x0 x1 x2 radius cube Physical.coordinateZ =
  subst
    (λ lower → lower ≤ radius + radius)
    (sym (adColumnZExact x0 x1 x2))
    (ℚP.+-mono-≤ (x1Bound cube) (x0Bound cube))

record CoordinateDifferenceCube
    (x0 x1 x2 y0 y1 y2 delta : ℚ) : Set where
  field
    d0Bound : ∣ x0 - y0 ∣ ≤ delta
    d1Bound : ∣ x1 - y1 ∣ ≤ delta
    d2Bound : ∣ x2 - y2 ∣ ≤ delta

open CoordinateDifferenceCube public

adDifferenceColumnBound :
  ∀ x0 x1 x2 y0 y1 y2 delta →
  CoordinateDifferenceCube x0 x1 x2 y0 y1 y2 delta →
  ∀ column →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    (Variation.matrixDifference
      (adMatrix x0 x1 x2) (adMatrix y0 y1 y2)) column
  ≤ delta + delta
adDifferenceColumnBound x0 x1 x2 y0 y1 y2 delta difference column =
  let
    exactMass :
      RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (Variation.matrixDifference
          (adMatrix x0 x1 x2) (adMatrix y0 y1 y2)) column
      ≡ RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (adMatrix (x0 - y0) (x1 - y1) (x2 - y2)) column
    exactMass =
      DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact.sumRationalCong
        Physical.lieCoordinates3 _ _
        (λ row → cong ∣_∣
          (adMatrixDifferenceExact x0 x1 x2 y0 y1 y2 row column))

    differenceCube : CoordinateCube
      (x0 - y0) (x1 - y1) (x2 - y2) delta
    differenceCube = record
      { x0Bound = d0Bound difference
      ; x1Bound = d1Bound difference
      ; x2Bound = d2Bound difference
      }
  in
  subst
    (λ lower → lower ≤ delta + delta)
    (sym exactMass)
    (adCoordinateCubeColumnBound
      (x0 - y0) (x1 - y1) (x2 - y2) delta differenceCube column)

cmp109SU2AdCoordinateMatrixLevel : ProofLevel
cmp109SU2AdCoordinateMatrixLevel = machineChecked

cmp109SU2AdCoordinateColumnMassLevel : ProofLevel
cmp109SU2AdCoordinateColumnMassLevel = machineChecked

cmp109SU2AdDifferenceColumnMassLevel : ProofLevel
cmp109SU2AdDifferenceColumnMassLevel = machineChecked
