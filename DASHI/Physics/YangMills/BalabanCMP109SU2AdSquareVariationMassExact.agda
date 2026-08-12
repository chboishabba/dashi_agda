module DASHI.Physics.YangMills.BalabanCMP109SU2AdSquareVariationMassExact where

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
-- Quantify the polynomial identity behind regularity of the inverse-dexp
-- Jacobian.  For A_X = ad_X,
--
--   A_X^2-A_Y^2
--     = (A_X-A_Y) A_X + A_Y (A_X-A_Y).
--
-- If every column of A_X and A_Y has mass <= C and every column of
-- A_X-A_Y has mass <= D, finite l1 composition gives
--
--   col(A_X^2) <= C^2,
--   col(A_X^2-A_Y^2) <= 2 C D.
--
-- At the coordinate estimate C=2 rho and D=2 delta this is exactly the
-- advertised 4 rho^2 and 8 rho delta budget.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanFiniteRectangularSchurSquaredExact as RectSchur
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanCMP109FederbushComponentResidualExact as Component
import DASHI.Physics.YangMills.BalabanCMP109FederbushComponentVariationExact as Variation
import DASHI.Physics.YangMills.BalabanCMP109FederbushResidualMassTelescopeExact as Mass

adSquare : Component.Jacobian.Lie3Matrix → Component.Jacobian.Lie3Matrix
adSquare ad = Component.matrixCompose ad ad

adSquareDifferenceExact : ∀ adX adY row column →
  Variation.matrixDifference (adSquare adX) (adSquare adY) row column
  ≡ Component.matrixCompose
      (Variation.matrixDifference adX adY) adX row column
    + Component.matrixCompose adY
      (Variation.matrixDifference adX adY) row column
adSquareDifferenceExact adX adY row column =
  Variation.componentProductVariationExact adX adX adY adY row column

adSquareColumnMassBound :
  ∀ ad bound column →
  0ℚ ≤ bound →
  (∀ selected →
    RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3 ad selected
    ≤ bound) →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    (adSquare ad) column
  ≤ bound * bound
adSquareColumnMassBound ad bound column boundNonnegative columns =
  Mass.composeColumnMassBound
    ad ad bound bound column boundNonnegative columns (columns column)

adSquareVariationColumnMassBound :
  ∀ adX adY normBound variationBound column →
  0ℚ ≤ normBound →
  0ℚ ≤ variationBound →
  (∀ selected →
    RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3 adX selected
    ≤ normBound) →
  (∀ selected →
    RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3 adY selected
    ≤ normBound) →
  (∀ selected →
    RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
      (Variation.matrixDifference adX adY) selected
    ≤ variationBound) →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    (Variation.matrixDifference (adSquare adX) (adSquare adY)) column
  ≤ (normBound * variationBound)
    + (normBound * variationBound)
adSquareVariationColumnMassBound
    adX adY normBound variationBound column
    normNonnegative variationNonnegative columnsX columnsY variationColumns =
  let
    first = Component.matrixCompose
      (Variation.matrixDifference adX adY) adX
    second = Component.matrixCompose adY
      (Variation.matrixDifference adX adY)

    firstBound :
      RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3 first column
      ≤ variationBound * normBound
    firstBound = Mass.composeColumnMassBound
      (Variation.matrixDifference adX adY) adX
      variationBound normBound column
      variationNonnegative variationColumns (columnsX column)

    secondBound :
      RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3 second column
      ≤ normBound * variationBound
    secondBound = Mass.composeColumnMassBound
      adY (Variation.matrixDifference adX adY)
      normBound variationBound column
      normNonnegative columnsY (variationColumns column)

    firstReordered :
      RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3 first column
      ≤ normBound * variationBound
    firstReordered = subst
      (λ upper →
        RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3 first column
        ≤ upper)
      (ℚP.*-comm variationBound normBound)
      firstBound

    pointwise :
      RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (Variation.matrixDifference (adSquare adX) (adSquare adY)) column
      ≤ Sums.sumRational Physical.lieCoordinates3
        (λ row → ∣ first row column ∣ + ∣ second row column ∣)
    pointwise = Schur.sumPointwiseBelow Physical.lieCoordinates3 _ _
      (λ row →
        subst
          (λ value →
            ∣ value ∣ ≤ ∣ first row column ∣ + ∣ second row column ∣)
          (adSquareDifferenceExact adX adY row column)
          (ℚP.∣p+q∣≤∣p∣+∣q∣
            (first row column) (second row column)))

    split :
      Sums.sumRational Physical.lieCoordinates3
        (λ row → ∣ first row column ∣ + ∣ second row column ∣)
      ≡ RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3 first column
        + RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3 second column
    split =
      DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact.sumRationalAdd
        Physical.lieCoordinates3
        (λ row → ∣ first row column ∣)
        (λ row → ∣ second row column ∣)

    triangle = subst
      (λ upper →
        RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
          (Variation.matrixDifference (adSquare adX) (adSquare adY)) column
        ≤ upper)
      split pointwise
  in
  ℚP.≤-trans triangle
    (ℚP.+-mono-≤ firstReordered secondBound)

coordinateBudgetSquareExact : ∀ radius →
  (radius + radius) * (radius + radius)
  ≡ (radius * radius + radius * radius)
    + (radius * radius + radius * radius)
coordinateBudgetSquareExact radius = ℚRing.solve-∀ radius

coordinateBudgetVariationExact : ∀ radius delta →
  ((radius + radius) * (delta + delta))
  + ((radius + radius) * (delta + delta))
  ≡ (((radius * delta + radius * delta)
      + (radius * delta + radius * delta))
    + ((radius * delta + radius * delta)
      + (radius * delta + radius * delta)))
coordinateBudgetVariationExact radius delta = ℚRing.solve-∀ radius delta

cmp109AdSquareVariationIdentityLevel : ProofLevel
cmp109AdSquareVariationIdentityLevel = machineChecked

cmp109AdSquareColumnMassLevel : ProofLevel
cmp109AdSquareColumnMassLevel = machineChecked

cmp109AdSquareVariationColumnMassLevel : ProofLevel
cmp109AdSquareVariationColumnMassLevel = machineChecked
