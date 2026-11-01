module DASHI.Physics.YangMills.BalabanCMP109FederbushInverseVariationMassExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators", Springer Classics in
-- Mathematics, 1995 reprint. DOI: 10.1007/978-3-642-66282-9.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- Combine the exact Lie3 resolvent identity with the same l1 column-mass
-- calculus used for the 1/4 Federbush reopening.  If both normalized
-- Federbush inverses have column mass at most 4/3 and
--
--   col(A_U-A_V) <= L_A d,
--
-- then
--
--   col(A_U^{-1}-A_V^{-1}) <= (16/9) L_A d.
--
-- The 16/9 is proved as exact rational arithmetic; no operator determinant or
-- finite-dimensional compactness argument enters.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _*_; _≤_; _/_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteRectangularSchurSquaredExact as RectSchur
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanCMP109FederbushQuarterReopeningExact as Quarter
import DASHI.Physics.YangMills.BalabanCMP109FederbushComponentResidualExact as Component
import DASHI.Physics.YangMills.BalabanCMP109FederbushComponentVariationExact as Variation
import DASHI.Physics.YangMills.BalabanCMP109FederbushResidualMassTelescopeExact as Mass
import DASHI.Physics.YangMills.BalabanCMP109Lie3ResolventIdentityExact as Resolvent

sixteenNinths : ℚ
sixteenNinths = + 16 / 9

fourThirdsSquaredExact : ∀ bound →
  (Quarter.fourThirds * bound) * Quarter.fourThirds
  ≡ sixteenNinths * bound
fourThirdsSquaredExact bound = ℚRing.solve-∀ bound

productNonnegative : ∀ left right →
  0ℚ ≤ left → 0ℚ ≤ right → 0ℚ ≤ left * right
productNonnegative = Schur.productNonnegative

inverseDifferenceColumnMassBound :
  ∀ matrixU inverseU matrixV inverseV variationBound column →
  Resolvent.TwoSidedInversePair matrixU inverseU →
  Resolvent.TwoSidedInversePair matrixV inverseV →
  0ℚ ≤ variationBound →
  (∀ selected →
    RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3 inverseU selected
    ≤ Quarter.fourThirds) →
  (∀ selected →
    RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3 inverseV selected
    ≤ Quarter.fourThirds) →
  (∀ selected →
    RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
      (Variation.matrixDifference matrixV matrixU) selected
    ≤ variationBound) →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    (Variation.matrixDifference inverseU inverseV) column
  ≤ sixteenNinths * variationBound
inverseDifferenceColumnMassBound
    matrixU inverseU matrixV inverseV variationBound column
    inversePairU inversePairV variationNonnegative
    inverseUColumns inverseVColumns variationColumns =
  let
    firstProduct = Component.matrixCompose inverseU
      (Variation.matrixDifference matrixV matrixU)

    firstBound : ∀ selected →
      RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        firstProduct selected
      ≤ Quarter.fourThirds * variationBound
    firstBound selected =
      Mass.composeColumnMassBound
        inverseU
        (Variation.matrixDifference matrixV matrixU)
        Quarter.fourThirds variationBound selected
        (ℚP.nonNegative⁻¹ Quarter.fourThirds)
        inverseUColumns
        (variationColumns selected)

    firstBoundNonnegative :
      0ℚ ≤ Quarter.fourThirds * variationBound
    firstBoundNonnegative = productNonnegative
      Quarter.fourThirds variationBound
      (ℚP.nonNegative⁻¹ Quarter.fourThirds)
      variationNonnegative

    raw :
      RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (Component.matrixCompose firstProduct inverseV) column
      ≤ (Quarter.fourThirds * variationBound) * Quarter.fourThirds
    raw =
      Mass.composeColumnMassBound
        firstProduct inverseV
        (Quarter.fourThirds * variationBound) Quarter.fourThirds column
        firstBoundNonnegative
        firstBound
        (inverseVColumns column)

    scaled :
      RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (Component.matrixCompose firstProduct inverseV) column
      ≤ sixteenNinths * variationBound
    scaled = subst
      (λ upper →
        RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
          (Component.matrixCompose firstProduct inverseV) column
        ≤ upper)
      (fourThirdsSquaredExact variationBound)
      raw

    massExact :
      RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (Variation.matrixDifference inverseU inverseV) column
      ≡ RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (Component.matrixCompose firstProduct inverseV) column
    massExact =
      Sums.sumRationalCong Physical.lieCoordinates3 _ _
        (λ row →
          cong ∣_∣
            (Resolvent.resolventDifferenceExact
              matrixU inverseU matrixV inverseV
              inversePairU inversePairV row column))
  in
  subst
    (λ lower → lower ≤ sixteenNinths * variationBound)
    (sym massExact)
    scaled

cmp109FederbushInverseVariationResolventLevel : ProofLevel
cmp109FederbushInverseVariationResolventLevel = machineChecked

cmp109FederbushInverseVariationSixteenNinthsLevel : ProofLevel
cmp109FederbushInverseVariationSixteenNinthsLevel = machineChecked
