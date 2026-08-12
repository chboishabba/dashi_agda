module DASHI.Physics.YangMills.BalabanCMP109SelectedBlockAverageIFTBridgeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Connect the already-prepared CMP109 four-stage derivative primitive to the
-- literal 12 x 3072 selected block-average Newton budget.  A primitive owns a
-- physical coordinate of `DQ_background-DQ_reference`, proves that coordinate
-- is dominated by its operator norm, and proves the full difference norm is
-- at most its radius.  Therefore a primitive whose radius is exactly
-- rho=1/8192 supplies, without another hypothesis,
--
--     |(DQ_background-DQ_reference)(row,column)| <= rho.
--
-- Two such primitives feed the rectangular Schur theorem from the preceding
-- module and yield the strict two-background bound
--
--     ||(DQ_U-DQ_A)h||^2 <= 9/4096 ||h||^2
--                          < 3711/262144 ||h||^2.
--
-- This removes all finite accumulation arithmetic from the nonlinear average
-- frontier.  The remaining physical seam is exact identification of the
-- printed CMP109 derivative coordinate with the selected nonlinear constraint
-- derivative entry at the same background; the source-level four-stage norm
-- pipeline and the finite IFT budget are now already connected.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (Product; pair)
import DASHI.Physics.YangMills.BalabanP33CMP109DerivativeDifferencePrimitiveExact as Primitive
import DASHI.Physics.YangMills.BalabanSelectedBackgroundBlockAverageConstraintMatrixExact as Average
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanSelectedBlockAverageReferenceEntryBudgetExact as Budget
import DASHI.Physics.YangMills.BalabanFiniteRectangularSchurSquaredExact as RectSchur
import DASHI.Physics.YangMills.BalabanSelectedGaugeDerivativeTwoBackgroundVariationExact as GaugeVariation

Row : Set
Row = Average.SelectedBlockAverageRow4

Column : Set
Column = Physical.PhysicalSU2Coordinate4

Cell : Set
Cell = Product Row Column

primitiveReferenceDifferenceMatrix :
  ∀ {Operator} →
  Primitive.CMP109DerivativeDifferencePrimitive Operator Cell →
  Budget.Matrix
primitiveReferenceDifferenceMatrix primitive row column =
  Primitive.blockDerivativeDifferenceCoordinate primitive (pair row column)

primitiveEntryBelowRadius :
  ∀ {Operator}
    (primitive : Primitive.CMP109DerivativeDifferencePrimitive Operator Cell)
    row column →
  ∣ primitiveReferenceDifferenceMatrix primitive row column ∣
  ≤ Primitive.radius primitive
primitiveEntryBelowRadius primitive row column =
  ℚP.≤-trans
    (Primitive.blockDerivativeCoordinateBelowNorm primitive (pair row column))
    (Primitive.blockDerivativeDifferenceNormBelowRadius primitive)

primitiveEntryBelowSelectedRho :
  ∀ {Operator}
    (primitive : Primitive.CMP109DerivativeDifferencePrimitive Operator Cell) →
  Primitive.radius primitive ≡ Budget.rho →
  ∀ row column →
  ∣ primitiveReferenceDifferenceMatrix primitive row column ∣ ≤ Budget.rho
primitiveEntryBelowSelectedRho primitive radiusExact row column =
  subst
    (λ upper →
      ∣ primitiveReferenceDifferenceMatrix primitive row column ∣ ≤ upper)
    radiusExact
    (primitiveEntryBelowRadius primitive row column)

cmp109TwoBackgroundPrimitivesGiveSelectedSchurBound :
  ∀ {LeftOperator RightOperator}
    (left : Primitive.CMP109DerivativeDifferencePrimitive LeftOperator Cell)
    (right : Primitive.CMP109DerivativeDifferencePrimitive RightOperator Cell)
    (vector : Budget.Vector) →
  Primitive.radius left ≡ Budget.rho →
  Primitive.radius right ≡ Budget.rho →
  RectSchur.rectVectorNormSq Budget.rows
    (RectSchur.rectApply Budget.columns
      (Budget.twoBackgroundMatrix
        (primitiveReferenceDifferenceMatrix left)
        (primitiveReferenceDifferenceMatrix right))
      vector)
  ≤ Budget.blockAverageSchurSquaredCoefficient
      * RectSchur.rectVectorNormSq Budget.columns vector
cmp109TwoBackgroundPrimitivesGiveSelectedSchurBound
    left right vector leftRadius rightRadius =
  Budget.selectedBlockAverageTwoBackgroundVariationSchur
    (primitiveReferenceDifferenceMatrix left)
    (primitiveReferenceDifferenceMatrix right)
    vector
    (primitiveEntryBelowSelectedRho left leftRadius)
    (primitiveEntryBelowSelectedRho right rightRadius)

cmp109TwoBackgroundPrimitivesFitSelectedIFTBudget :
  ∀ {LeftOperator RightOperator}
    (left : Primitive.CMP109DerivativeDifferencePrimitive LeftOperator Cell)
    (right : Primitive.CMP109DerivativeDifferencePrimitive RightOperator Cell)
    (vector : Budget.Vector) →
  Primitive.radius left ≡ Budget.rho →
  Primitive.radius right ≡ Budget.rho →
  RectSchur.rectVectorNormSq Budget.rows
    (RectSchur.rectApply Budget.columns
      (Budget.twoBackgroundMatrix
        (primitiveReferenceDifferenceMatrix left)
        (primitiveReferenceDifferenceMatrix right))
      vector)
  ≤ GaugeVariation.blockAverageDerivativeRemainingSquaredBudget
      * RectSchur.rectVectorNormSq Budget.columns vector
cmp109TwoBackgroundPrimitivesFitSelectedIFTBudget
    left right vector leftRadius rightRadius =
  Budget.selectedBlockAverageTwoBackgroundFitsIFTBudget
    (primitiveReferenceDifferenceMatrix left)
    (primitiveReferenceDifferenceMatrix right)
    vector
    (primitiveEntryBelowSelectedRho left leftRadius)
    (primitiveEntryBelowSelectedRho right rightRadius)

cmp109PrimitiveToSelectedReferenceEntryLevel : ProofLevel
cmp109PrimitiveToSelectedReferenceEntryLevel = machineChecked

cmp109TwoBackgroundSelectedSchurLevel : ProofLevel
cmp109TwoBackgroundSelectedSchurLevel = machineChecked

cmp109TwoBackgroundSelectedIFTBudgetLevel : ProofLevel
cmp109TwoBackgroundSelectedIFTBudgetLevel = machineChecked

physicalCMP109SelectedDerivativeEntrySameObjectLevel : ProofLevel
physicalCMP109SelectedDerivativeEntrySameObjectLevel = conditional
