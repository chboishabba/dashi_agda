module DASHI.Physics.YangMills.BalabanP33PrimitiveOperatorNormLocalBoundsExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Ethan Eade,
-- "Derivative of the Exponential Map", technical note, 2018 revision.
-- No DOI recorded.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- DASHI CONTRIBUTION
--
-- This file performs the sign-sensitive quantitative step between primitive
-- operator-norm estimates and the five local Hessian coefficients.  A matrix
-- coefficient of an operator defect is trapped between plus/minus the operator
-- norm.  The primitive estimates are then allocated as
--
--   curvature   : 32 ||Ad(exp X)-I||,
--   transport   : 32 ||Ad(exp X)-I||
--               + 16 (||dexp_X-I|| + ||dexp_X^-1-I||),
--   chart       : 16 (||dexp_X-I|| + ||dexp_X^-1-I||),
--   gauge       : 32 (||d_A-d|| + ||d_A^*-d^*||),
--   constraint  : 64 ||DQ_A-DQ_0||.
--
-- Under the normalized primitive budgets
--
--   ||Ad-I|| <= rho,
--   ||dexp-I|| + ||dexp^-1-I|| <= 2 rho,
--   ||d_A-d|| + ||d_A^*-d^*|| <= 2 rho,
--   ||DQ_A-DQ_0|| <= rho,
--
-- the exact channel constants are 32, 64, 32, 64 and 64.  No global Hessian
-- estimate is assumed here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _≤_; NonNegative; Positive; pos)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT3ConfiguredGeometricConstantsExact as Constants

------------------------------------------------------------------------
-- Concrete positivity of the configured integer coefficients.
------------------------------------------------------------------------

instance
  onePositive : Positive 1ℚ
  onePositive = pos

  twoPositive : Positive Constants.twoℚ
  twoPositive = ℚP.pos+pos⇒pos 1ℚ 1ℚ

  fourPositive : Positive Constants.fourℚ
  fourPositive = ℚP.pos+pos⇒pos Constants.twoℚ Constants.twoℚ

  eightPositive : Positive Constants.eightℚ
  eightPositive = ℚP.pos+pos⇒pos Constants.fourℚ Constants.fourℚ

  sixteenPositive : Positive Constants.sixteenℚ
  sixteenPositive = ℚP.pos+pos⇒pos Constants.eightℚ Constants.eightℚ

  thirtyTwoPositive : Positive Constants.thirtyTwoℚ
  thirtyTwoPositive =
    ℚP.pos+pos⇒pos Constants.sixteenℚ Constants.sixteenℚ

  sixtyFourPositive : Positive Constants.sixtyFourℚ
  sixtyFourPositive =
    ℚP.pos+pos⇒pos Constants.thirtyTwoℚ Constants.thirtyTwoℚ

  sixteenNonnegative : NonNegative Constants.sixteenℚ
  sixteenNonnegative = ℚP.pos⇒nonNeg Constants.sixteenℚ

  thirtyTwoNonnegative : NonNegative Constants.thirtyTwoℚ
  thirtyTwoNonnegative = ℚP.pos⇒nonNeg Constants.thirtyTwoℚ

  sixtyFourNonnegative : NonNegative Constants.sixtyFourℚ
  sixtyFourNonnegative = ℚP.pos⇒nonNeg Constants.sixtyFourℚ

------------------------------------------------------------------------
-- Ordered scalar lemmas used by every channel.
------------------------------------------------------------------------

negScale : ∀ scale value →
  scale * (- value) ≡ - (scale * value)
negScale = ℚRing.solve-∀

negAdd : ∀ left right →
  (- left) + (- right) ≡ - (left + right)
negAdd = ℚRing.solve-∀

scaleTwo : ∀ scale radius →
  scale * (Constants.twoℚ * radius)
  ≡ (scale + scale) * radius
scaleTwo = ℚRing.solve-∀

thirtyTwoPlusThirtyTwo : ∀ radius →
  Constants.thirtyTwoℚ * radius
  + Constants.thirtyTwoℚ * radius
  ≡ Constants.sixtyFourℚ * radius
thirtyTwoPlusThirtyTwo = ℚRing.solve-∀

record TwoSided (value budget : ℚ) : Set where
  field
    lower : - budget ≤ value
    upper : value ≤ budget

open TwoSided public

scaleTwoSided :
  ∀ scale {{_ : NonNegative scale}} value budget →
  TwoSided value budget →
  TwoSided (scale * value) (scale * budget)
scaleTwoSided scale value budget bound = record
  { lower =
      subst
        (λ left → left ≤ scale * value)
        (negScale scale budget)
        (ℚP.*-monoˡ-≤-nonNeg scale (lower bound))
  ; upper =
      ℚP.*-monoˡ-≤-nonNeg scale (upper bound)
  }

addTwoSided :
  ∀ left right leftBudget rightBudget →
  TwoSided left leftBudget →
  TwoSided right rightBudget →
  TwoSided (left + right) (leftBudget + rightBudget)
addTwoSided left right leftBudget rightBudget leftBound rightBound = record
  { lower =
      subst
        (λ lowerValue → lowerValue ≤ left + right)
        (negAdd leftBudget rightBudget)
        (ℚP.+-mono-≤ (lower leftBound) (lower rightBound))
  ; upper =
      ℚP.+-mono-≤ (upper leftBound) (upper rightBound)
  }

tightenTwoSided :
  ∀ value small large →
  small ≤ large →
  TwoSided value small →
  TwoSided value large
tightenTwoSided value small large small≤large bound = record
  { lower =
      ℚP.≤-trans
        (ℚP.neg-antimono-≤ small≤large)
        (lower bound)
  ; upper =
      ℚP.≤-trans (upper bound) small≤large
  }

scaledCoordinateFromNormBudget :
  ∀ scale {{_ : NonNegative scale}}
    coordinate normValue finalBudget →
  TwoSided coordinate normValue →
  normValue ≤ finalBudget →
  TwoSided (scale * coordinate) (scale * finalBudget)
scaledCoordinateFromNormBudget scale coordinate normValue finalBudget
    coordinateBound normBound =
  tightenTwoSided
    (scale * coordinate)
    (scale * normValue)
    (scale * finalBudget)
    (ℚP.*-monoˡ-≤-nonNeg scale normBound)
    (scaleTwoSided scale coordinate normValue coordinateBound)

pairedScaledCoordinateFromNormBudget :
  ∀ scale {{_ : NonNegative scale}}
    left right leftNorm rightNorm finalBudget →
  TwoSided left leftNorm →
  TwoSided right rightNorm →
  leftNorm + rightNorm ≤ finalBudget →
  TwoSided
    (scale * left + scale * right)
    (scale * finalBudget)
pairedScaledCoordinateFromNormBudget
    scale left right leftNorm rightNorm finalBudget
    leftBound rightBound normBound =
  tightenTwoSided
    (scale * left + scale * right)
    (scale * leftNorm + scale * rightNorm)
    (scale * finalBudget)
    (subst
      (λ lowerBudget → lowerBudget ≤ scale * finalBudget)
      (ℚP.*-distribˡ-+ scale leftNorm rightNorm)
      (ℚP.*-monoˡ-≤-nonNeg scale normBound))
    (addTwoSided
      (scale * left)
      (scale * right)
      (scale * leftNorm)
      (scale * rightNorm)
      (scaleTwoSided scale left leftNorm leftBound)
      (scaleTwoSided scale right rightNorm rightBound))

------------------------------------------------------------------------
-- Primitive physical operator norms and their literal coordinate projections.
------------------------------------------------------------------------

record PrimitivePhysicalOperatorNorms (Cell : Set) : Set₁ where
  field
    radius : ℚ
    radiusNonnegative : 0ℚ ≤ radius

    adDefect dexpDefect inverseDexpDefect : Cell → ℚ
    covariantDefect covariantAdjointDefect blockDerivativeDefect : Cell → ℚ

    adNorm dexpNorm inverseDexpNorm : Cell → ℚ
    covariantNorm covariantAdjointNorm blockDerivativeNorm : Cell → ℚ

    adCoordinateBound : ∀ cell →
      TwoSided (adDefect cell) (adNorm cell)
    dexpCoordinateBound : ∀ cell →
      TwoSided (dexpDefect cell) (dexpNorm cell)
    inverseDexpCoordinateBound : ∀ cell →
      TwoSided (inverseDexpDefect cell) (inverseDexpNorm cell)
    covariantCoordinateBound : ∀ cell →
      TwoSided (covariantDefect cell) (covariantNorm cell)
    covariantAdjointCoordinateBound : ∀ cell →
      TwoSided (covariantAdjointDefect cell) (covariantAdjointNorm cell)
    blockDerivativeCoordinateBound : ∀ cell →
      TwoSided (blockDerivativeDefect cell) (blockDerivativeNorm cell)

    adOperatorBound : ∀ cell →
      adNorm cell ≤ radius

    dexpPairOperatorBound : ∀ cell →
      dexpNorm cell + inverseDexpNorm cell
      ≤ Constants.twoℚ * radius

    covariantPairOperatorBound : ∀ cell →
      covariantNorm cell + covariantAdjointNorm cell
      ≤ Constants.twoℚ * radius

    blockDerivativeOperatorBound : ∀ cell →
      blockDerivativeNorm cell ≤ radius

open PrimitivePhysicalOperatorNorms public

------------------------------------------------------------------------
-- Exact local coefficients of the five mechanisms.
------------------------------------------------------------------------

curvatureCoefficient :
  ∀ {Cell} → PrimitivePhysicalOperatorNorms Cell → Cell → ℚ
curvatureCoefficient dataSet cell =
  Constants.thirtyTwoℚ * adDefect dataSet cell

transportCoefficient :
  ∀ {Cell} → PrimitivePhysicalOperatorNorms Cell → Cell → ℚ
transportCoefficient dataSet cell =
  Constants.thirtyTwoℚ * adDefect dataSet cell
  + (Constants.sixteenℚ * dexpDefect dataSet cell
  + Constants.sixteenℚ * inverseDexpDefect dataSet cell)

chartCoefficient :
  ∀ {Cell} → PrimitivePhysicalOperatorNorms Cell → Cell → ℚ
chartCoefficient dataSet cell =
  Constants.sixteenℚ * dexpDefect dataSet cell
  + Constants.sixteenℚ * inverseDexpDefect dataSet cell

gaugeCoefficient :
  ∀ {Cell} → PrimitivePhysicalOperatorNorms Cell → Cell → ℚ
gaugeCoefficient dataSet cell =
  Constants.thirtyTwoℚ * covariantDefect dataSet cell
  + Constants.thirtyTwoℚ * covariantAdjointDefect dataSet cell

constraintCoefficient :
  ∀ {Cell} → PrimitivePhysicalOperatorNorms Cell → Cell → ℚ
constraintCoefficient dataSet cell =
  Constants.sixtyFourℚ * blockDerivativeDefect dataSet cell

------------------------------------------------------------------------
-- The five requested pointwise coefficient estimates.
------------------------------------------------------------------------

curvatureCoefficientBound :
  ∀ {Cell} (dataSet : PrimitivePhysicalOperatorNorms Cell) cell →
  TwoSided
    (curvatureCoefficient dataSet cell)
    (Constants.configuredCurvatureCoefficient * radius dataSet)
curvatureCoefficientBound dataSet cell =
  scaledCoordinateFromNormBudget
    Constants.thirtyTwoℚ
    (adDefect dataSet cell)
    (adNorm dataSet cell)
    (radius dataSet)
    (adCoordinateBound dataSet cell)
    (adOperatorBound dataSet cell)

chartCoefficientBound :
  ∀ {Cell} (dataSet : PrimitivePhysicalOperatorNorms Cell) cell →
  TwoSided
    (chartCoefficient dataSet cell)
    (Constants.configuredChartCoefficient * radius dataSet)
chartCoefficientBound dataSet cell =
  subst
    (TwoSided (chartCoefficient dataSet cell))
    (scaleTwo Constants.sixteenℚ (radius dataSet))
    (pairedScaledCoordinateFromNormBudget
      Constants.sixteenℚ
      (dexpDefect dataSet cell)
      (inverseDexpDefect dataSet cell)
      (dexpNorm dataSet cell)
      (inverseDexpNorm dataSet cell)
      (Constants.twoℚ * radius dataSet)
      (dexpCoordinateBound dataSet cell)
      (inverseDexpCoordinateBound dataSet cell)
      (dexpPairOperatorBound dataSet cell))

transportCoefficientBound :
  ∀ {Cell} (dataSet : PrimitivePhysicalOperatorNorms Cell) cell →
  TwoSided
    (transportCoefficient dataSet cell)
    (Constants.configuredTransportCoefficient * radius dataSet)
transportCoefficientBound dataSet cell =
  subst
    (TwoSided (transportCoefficient dataSet cell))
    (thirtyTwoPlusThirtyTwo (radius dataSet))
    (addTwoSided
      (curvatureCoefficient dataSet cell)
      (chartCoefficient dataSet cell)
      (Constants.thirtyTwoℚ * radius dataSet)
      (Constants.thirtyTwoℚ * radius dataSet)
      (curvatureCoefficientBound dataSet cell)
      (chartCoefficientBound dataSet cell))

gaugeCoefficientBound :
  ∀ {Cell} (dataSet : PrimitivePhysicalOperatorNorms Cell) cell →
  TwoSided
    (gaugeCoefficient dataSet cell)
    (Constants.configuredGaugeCoefficient * radius dataSet)
gaugeCoefficientBound dataSet cell =
  subst
    (TwoSided (gaugeCoefficient dataSet cell))
    (scaleTwo Constants.thirtyTwoℚ (radius dataSet))
    (pairedScaledCoordinateFromNormBudget
      Constants.thirtyTwoℚ
      (covariantDefect dataSet cell)
      (covariantAdjointDefect dataSet cell)
      (covariantNorm dataSet cell)
      (covariantAdjointNorm dataSet cell)
      (Constants.twoℚ * radius dataSet)
      (covariantCoordinateBound dataSet cell)
      (covariantAdjointCoordinateBound dataSet cell)
      (covariantPairOperatorBound dataSet cell))

constraintCoefficientBound :
  ∀ {Cell} (dataSet : PrimitivePhysicalOperatorNorms Cell) cell →
  TwoSided
    (constraintCoefficient dataSet cell)
    (Constants.configuredConstraintCoefficient * radius dataSet)
constraintCoefficientBound dataSet cell =
  scaledCoordinateFromNormBudget
    Constants.sixtyFourℚ
    (blockDerivativeDefect dataSet cell)
    (blockDerivativeNorm dataSet cell)
    (radius dataSet)
    (blockDerivativeCoordinateBound dataSet cell)
    (blockDerivativeOperatorBound dataSet cell)

primitiveCoordinateProjectionLevel : ProofLevel
primitiveCoordinateProjectionLevel = machineChecked

fiveMechanismCoefficientAllocationLevel : ProofLevel
fiveMechanismCoefficientAllocationLevel = machineChecked

fiveMechanismSignedCoefficientBoundsLevel : ProofLevel
fiveMechanismSignedCoefficientBoundsLevel = machineChecked
