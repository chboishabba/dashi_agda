module DASHI.Physics.YangMills.BalabanCMP109PrincipalLogDefectFromEndpointModulusExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University (2022), arXiv:2205.08354.
-- No DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Specialize the checked principal-log local Lipschitz theorem against the
-- zero Lie-algebra endpoint.  The polynomial inverse-dexp representation is
--
--   J_X = I + c1 ad_X + c2(X) ad_X^2,
--
-- and J_0=I exactly.  On the calibrated radius delta=rho/96, it is enough to
-- know the deliberately weak scalar coefficient modulus
--
--   |c2(X)-1/12| <= delta
--
-- together with |c1|<=1/2 and the coordinate delta-cube.  Then
--
--   col(J_X-I) <= (5/3+1) delta = (8/3) delta < rho/8.
--
-- Thus the remaining principal-log leaf is scalar/coordinate data, not an
-- independently supplied 3x3 matrix estimate.  The Bishop endpoint theorem in
-- the repository is much stronger, O(t^2/100); this module is the rational
-- consumer needed to connect it to the Federbush inverse lane.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _/_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteRectangularSchurSquaredExact as RectSchur
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedJacobianExact as Jacobian
import DASHI.Physics.YangMills.BalabanCMP109FederbushComponentResidualExact as Component
import DASHI.Physics.YangMills.BalabanCMP109FederbushComponentVariationExact as Variation
import DASHI.Physics.YangMills.BalabanCMP109SU2AdCoordinateMassExact as Ad
import DASHI.Physics.YangMills.BalabanCMP109SU2AdSquareVariationMassExact as AdSq
import DASHI.Physics.YangMills.BalabanCMP109SU2PrincipalLogAdPolynomialVariationMassExact as JVar
import DASHI.Physics.YangMills.BalabanCMP109SU2PrincipalLogLocalLipschitzExact as Local
import DASHI.Physics.YangMills.BalabanP33CMP109LocalLeafCalibrationExact as Calibration
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

c2AtZero one : ℚ
c2AtZero = + 1 / 12
one = + 1 / 1

zeroAd : Jacobian.Lie3Matrix
zeroAd = Ad.adMatrix 0ℚ 0ℚ 0ℚ

zeroAdSquare : Jacobian.Lie3Matrix
zeroAdSquare = AdSq.adSquare zeroAd

principalLogAtZeroIsIdentity : ∀ c1 row column →
  JVar.principalLogAdMatrix c1 c2AtZero zeroAd zeroAdSquare row column
  ≡ Jacobian.identity3 row column
principalLogAtZeroIsIdentity c1 Physical.coordinateX Physical.coordinateX =
  ℚRing.solve-∀ c1
principalLogAtZeroIsIdentity c1 Physical.coordinateX Physical.coordinateY =
  ℚRing.solve-∀ c1
principalLogAtZeroIsIdentity c1 Physical.coordinateX Physical.coordinateZ =
  ℚRing.solve-∀ c1
principalLogAtZeroIsIdentity c1 Physical.coordinateY Physical.coordinateX =
  ℚRing.solve-∀ c1
principalLogAtZeroIsIdentity c1 Physical.coordinateY Physical.coordinateY =
  ℚRing.solve-∀ c1
principalLogAtZeroIsIdentity c1 Physical.coordinateY Physical.coordinateZ =
  ℚRing.solve-∀ c1
principalLogAtZeroIsIdentity c1 Physical.coordinateZ Physical.coordinateX =
  ℚRing.solve-∀ c1
principalLogAtZeroIsIdentity c1 Physical.coordinateZ Physical.coordinateY =
  ℚRing.solve-∀ c1
principalLogAtZeroIsIdentity c1 Physical.coordinateZ Physical.coordinateZ =
  ℚRing.solve-∀ c1

record PrincipalLogEndpointData
    (c1 c2X x0 x1 x2 : ℚ) : Set where
  field
    xCube : Ad.CoordinateCube
      x0 x1 x2 Calibration.logarithmChartRadius
    differenceFromZeroCube : Ad.CoordinateDifferenceCube
      x0 x1 x2 0ℚ 0ℚ 0ℚ Calibration.logarithmChartRadius
    c1AbsoluteBound : ∣ c1 ∣ ≤ Local.oneHalf
    coefficientEndpointModulus :
      ∣ JVar._-_ c2X c2AtZero ∣ ≤ Calibration.logarithmChartRadius

open PrincipalLogEndpointData public

zeroCube :
  Ad.CoordinateCube 0ℚ 0ℚ 0ℚ Calibration.logarithmChartRadius
zeroCube = record
  { Ad.CoordinateCube.x0Bound = ℚP.nonNegative⁻¹ Calibration.logarithmChartRadius
  ; Ad.CoordinateCube.x1Bound = ℚP.nonNegative⁻¹ Calibration.logarithmChartRadius
  ; Ad.CoordinateCube.x2Bound = ℚP.nonNegative⁻¹ Calibration.logarithmChartRadius
  }

logarithmRadiusBelowHalf : Calibration.logarithmChartRadius ≤ Local.oneHalf
logarithmRadiusBelowHalf =
  Norm.nonnegativeDifferenceImpliesBelow
    (ℚP.nonNegative⁻¹
      (Local.oneHalf - Calibration.logarithmChartRadius))

c2AtZeroBelowOneSixth : ∣ c2AtZero ∣ ≤ Local.oneSixth
c2AtZeroBelowOneSixth =
  Norm.nonnegativeDifferenceImpliesBelow
    (ℚP.nonNegative⁻¹ (Local.oneSixth - ∣ c2AtZero ∣))

asLocalModulusData :
  ∀ c1 c2X x0 x1 x2 →
  PrincipalLogEndpointData c1 c2X x0 x1 x2 →
  Local.PrincipalLogLocalModulusData
    c1 c2X c2AtZero
    x0 x1 x2 0ℚ 0ℚ 0ℚ
    Calibration.logarithmChartRadius
    Calibration.logarithmChartRadius one
asLocalModulusData c1 c2X x0 x1 x2 dataSet = record
  { Local.PrincipalLogLocalModulusData.rhoNonnegative =
      ℚP.nonNegative⁻¹ Calibration.logarithmChartRadius
  ; Local.PrincipalLogLocalModulusData.deltaNonnegative =
      ℚP.nonNegative⁻¹ Calibration.logarithmChartRadius
  ; Local.PrincipalLogLocalModulusData.L2Nonnegative =
      ℚP.nonNegative⁻¹ one
  ; Local.PrincipalLogLocalModulusData.rhoBelowHalf =
      logarithmRadiusBelowHalf
  ; Local.PrincipalLogLocalModulusData.xCube = xCube dataSet
  ; Local.PrincipalLogLocalModulusData.yCube = zeroCube
  ; Local.PrincipalLogLocalModulusData.differenceCube =
      differenceFromZeroCube dataSet
  ; Local.PrincipalLogLocalModulusData.c1AbsoluteBound =
      c1AbsoluteBound dataSet
  ; Local.PrincipalLogLocalModulusData.c2YAbsoluteBound =
      c2AtZeroBelowOneSixth
  ; Local.PrincipalLogLocalModulusData.c2DifferenceModulus =
      subst
        (λ upper → ∣ JVar._-_ c2X c2AtZero ∣ ≤ upper)
        (sym (ℚP.*-identityˡ Calibration.logarithmChartRadius))
        (coefficientEndpointModulus dataSet)
  }

principalLogVariationFromZeroColumn :
  ∀ c1 c2X x0 x1 x2 →
  PrincipalLogEndpointData c1 c2X x0 x1 x2 →
  ∀ column →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    (Variation.matrixDifference
      (JVar.principalLogAdMatrix
        c1 c2X
        (Ad.adMatrix x0 x1 x2)
        (AdSq.adSquare (Ad.adMatrix x0 x1 x2)))
      (JVar.principalLogAdMatrix
        c1 c2AtZero zeroAd zeroAdSquare)) column
  ≤ (Local.fiveThirds + one) * Calibration.logarithmChartRadius
principalLogVariationFromZeroColumn c1 c2X x0 x1 x2 dataSet =
  Local.principalLogLocalLipschitzColumn
    c1 c2X c2AtZero
    x0 x1 x2 0ℚ 0ℚ 0ℚ
    Calibration.logarithmChartRadius
    Calibration.logarithmChartRadius one
    (asLocalModulusData c1 c2X x0 x1 x2 dataSet)

localLipschitzFitsLogarithmAllocation :
  (Local.fiveThirds + one) * Calibration.logarithmChartRadius
  ≤ Calibration.logarithmAllocation
localLipschitzFitsLogarithmAllocation =
  Norm.nonnegativeDifferenceImpliesBelow
    (ℚP.nonNegative⁻¹
      (Calibration.logarithmAllocation
        - (Local.fiveThirds + one) * Calibration.logarithmChartRadius))

principalLogResidualColumnWithinAllocation :
  ∀ c1 c2X x0 x1 x2 →
  PrincipalLogEndpointData c1 c2X x0 x1 x2 →
  ∀ column →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    (Component.logJacobianResidual
      (JVar.principalLogAdMatrix
        c1 c2X
        (Ad.adMatrix x0 x1 x2)
        (AdSq.adSquare (Ad.adMatrix x0 x1 x2)))) column
  ≤ Calibration.logarithmAllocation
principalLogResidualColumnWithinAllocation
    c1 c2X x0 x1 x2 dataSet column =
  let
    current = JVar.principalLogAdMatrix
      c1 c2X
      (Ad.adMatrix x0 x1 x2)
      (AdSq.adSquare (Ad.adMatrix x0 x1 x2))
    zero = JVar.principalLogAdMatrix c1 c2AtZero zeroAd zeroAdSquare

    raw = principalLogVariationFromZeroColumn
      c1 c2X x0 x1 x2 dataSet column

    identify :
      RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (Variation.matrixDifference current zero) column
      ≡ RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (Component.logJacobianResidual current) column
    identify = Sums.sumRationalCong Physical.lieCoordinates3 _ _
      (λ row →
        cong ∣_∣
          (subst
            (λ reference →
              current row column - reference
              ≡ current row column - Jacobian.identity3 row column)
            (principalLogAtZeroIsIdentity c1 row column)
            refl))
  in
  ℚP.≤-trans
    (subst
      (λ lower →
        lower
        ≤ (Local.fiveThirds + one) * Calibration.logarithmChartRadius)
      identify raw)
    localLipschitzFitsLogarithmAllocation

cmp109PrincipalLogZeroEndpointIdentityLevel : ProofLevel
cmp109PrincipalLogZeroEndpointIdentityLevel = machineChecked

cmp109PrincipalLogEndpointModulusToDefectLevel : ProofLevel
cmp109PrincipalLogEndpointModulusToDefectLevel = machineChecked

-- Remaining scalar bridge: instantiate c1,c2X with the actual principal-log /
-- inverse-dexp coefficients and transport the already checked Bishop endpoint
-- modulus into the rational inequality used above.
cmp109PrincipalLogBishopCoefficientToRationalLevel : ProofLevel
cmp109PrincipalLogBishopCoefficientToRationalLevel = conditional
