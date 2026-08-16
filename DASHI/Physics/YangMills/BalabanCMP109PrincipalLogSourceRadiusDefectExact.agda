module DASHI.Physics.YangMills.BalabanCMP109PrincipalLogSourceRadiusDefectExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University (2022), arXiv:2205.08354.
-- No DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Run the existing finite l1 principal-log Lipschitz theorem on the FULL CMP98
-- source chart t=1/12 rather than on the tiny rho/96 calibration.
--
-- The Bishop endpoint work gives the scalar quadratic modulus
--
--       |c2(Y)-1/12| <= t^2/100.
--
-- At t=1/12 this is exactly (1/1200)t = 1/14400.  Hence, with
-- |c1|<=1/2 and each Lie coordinate bounded by t, the checked matrix theorem
-- gives
--
--       col(J_Y-I) <= (5/3 + 1/1200)t < 1/4.
--
-- This deliberately uses a coarse coordinate-l1 estimate.  It is nevertheless
-- already strong enough for the dexp/transport cancellation route, and avoids
-- claiming the sharper t/2+t^2/6 matrix envelope before its norm dictionary is
-- formalized.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _/_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst)

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
import DASHI.Physics.YangMills.BalabanCMP109FederbushQuarterReopeningExact as Quarter
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

sourceRadius : ℚ
sourceRadius = + 1 / 12

sourceCoefficientLipschitz : ℚ
sourceCoefficientLipschitz = + 1 / 1200

sourceCoefficientEndpointAllowance : ℚ
sourceCoefficientEndpointAllowance = sourceCoefficientLipschitz * sourceRadius

sourceCoefficientEndpointAllowanceIsOne14400 :
  sourceCoefficientEndpointAllowance ≡ + 1 / 14400
sourceCoefficientEndpointAllowanceIsOne14400 = ℚRing.solve []

sourcePrincipalLogColumnBound : ℚ
sourcePrincipalLogColumnBound =
  (Local.fiveThirds + sourceCoefficientLipschitz) * sourceRadius

sourcePrincipalLogColumnFitsQuarter :
  sourcePrincipalLogColumnBound ≤ Quarter.oneQuarter
sourcePrincipalLogColumnFitsQuarter =
  Norm.nonnegativeDifferenceImpliesBelow
    (ℚP.nonNegative⁻¹
      (Quarter.oneQuarter - sourcePrincipalLogColumnBound))

zeroAd : Jacobian.Lie3Matrix
zeroAd = Ad.adMatrix 0ℚ 0ℚ 0ℚ

zeroAdSquare : Jacobian.Lie3Matrix
zeroAdSquare = AdSq.adSquare zeroAd

c2AtZero : ℚ
c2AtZero = + 1 / 12

principalLogAtZeroIsIdentity : ∀ c1 row column →
  JVar.principalLogAdMatrix c1 c2AtZero zeroAd zeroAdSquare row column
  ≡ Jacobian.identity3 row column
principalLogAtZeroIsIdentity c1 Physical.coordinateX Physical.coordinateX = ℚRing.solve-∀ c1
principalLogAtZeroIsIdentity c1 Physical.coordinateX Physical.coordinateY = ℚRing.solve-∀ c1
principalLogAtZeroIsIdentity c1 Physical.coordinateX Physical.coordinateZ = ℚRing.solve-∀ c1
principalLogAtZeroIsIdentity c1 Physical.coordinateY Physical.coordinateX = ℚRing.solve-∀ c1
principalLogAtZeroIsIdentity c1 Physical.coordinateY Physical.coordinateY = ℚRing.solve-∀ c1
principalLogAtZeroIsIdentity c1 Physical.coordinateY Physical.coordinateZ = ℚRing.solve-∀ c1
principalLogAtZeroIsIdentity c1 Physical.coordinateZ Physical.coordinateX = ℚRing.solve-∀ c1
principalLogAtZeroIsIdentity c1 Physical.coordinateZ Physical.coordinateY = ℚRing.solve-∀ c1
principalLogAtZeroIsIdentity c1 Physical.coordinateZ Physical.coordinateZ = ℚRing.solve-∀ c1

record SourceRadiusPrincipalLogData
    (c1 c2 x0 x1 x2 : ℚ) : Set where
  field
    coordinateCube : Ad.CoordinateCube x0 x1 x2 sourceRadius
    differenceFromZeroCube :
      Ad.CoordinateDifferenceCube x0 x1 x2 0ℚ 0ℚ 0ℚ sourceRadius
    c1AbsoluteBound : ∣ c1 ∣ ≤ Local.oneHalf
    coefficientEndpointModulus :
      ∣ c2 - c2AtZero ∣ ≤ sourceCoefficientEndpointAllowance

open SourceRadiusPrincipalLogData public

zeroCube : Ad.CoordinateCube 0ℚ 0ℚ 0ℚ sourceRadius
zeroCube = record
  { Ad.CoordinateCube.x0Bound = ℚP.nonNegative⁻¹ sourceRadius
  ; Ad.CoordinateCube.x1Bound = ℚP.nonNegative⁻¹ sourceRadius
  ; Ad.CoordinateCube.x2Bound = ℚP.nonNegative⁻¹ sourceRadius
  }

sourceRadiusBelowHalf : sourceRadius ≤ Local.oneHalf
sourceRadiusBelowHalf =
  Norm.nonnegativeDifferenceImpliesBelow
    (ℚP.nonNegative⁻¹ (Local.oneHalf - sourceRadius))

c2AtZeroBelowOneSixth : ∣ c2AtZero ∣ ≤ Local.oneSixth
c2AtZeroBelowOneSixth =
  Norm.nonnegativeDifferenceImpliesBelow
    (ℚP.nonNegative⁻¹ (Local.oneSixth - ∣ c2AtZero ∣))

asLocalModulusData :
  ∀ c1 c2 x0 x1 x2 →
  SourceRadiusPrincipalLogData c1 c2 x0 x1 x2 →
  Local.PrincipalLogLocalModulusData
    c1 c2 c2AtZero
    x0 x1 x2 0ℚ 0ℚ 0ℚ
    sourceRadius sourceRadius sourceCoefficientLipschitz
asLocalModulusData c1 c2 x0 x1 x2 dataSet = record
  { Local.PrincipalLogLocalModulusData.rhoNonnegative =
      ℚP.nonNegative⁻¹ sourceRadius
  ; Local.PrincipalLogLocalModulusData.deltaNonnegative =
      ℚP.nonNegative⁻¹ sourceRadius
  ; Local.PrincipalLogLocalModulusData.L2Nonnegative =
      ℚP.nonNegative⁻¹ sourceCoefficientLipschitz
  ; Local.PrincipalLogLocalModulusData.rhoBelowHalf = sourceRadiusBelowHalf
  ; Local.PrincipalLogLocalModulusData.xCube = coordinateCube dataSet
  ; Local.PrincipalLogLocalModulusData.yCube = zeroCube
  ; Local.PrincipalLogLocalModulusData.differenceCube =
      differenceFromZeroCube dataSet
  ; Local.PrincipalLogLocalModulusData.c1AbsoluteBound = c1AbsoluteBound dataSet
  ; Local.PrincipalLogLocalModulusData.c2YAbsoluteBound =
      c2AtZeroBelowOneSixth
  ; Local.PrincipalLogLocalModulusData.c2DifferenceModulus =
      coefficientEndpointModulus dataSet
  }

sourcePrincipalLogVariationColumn :
  ∀ c1 c2 x0 x1 x2 →
  SourceRadiusPrincipalLogData c1 c2 x0 x1 x2 →
  ∀ column →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    (Variation.matrixDifference
      (JVar.principalLogAdMatrix
        c1 c2
        (Ad.adMatrix x0 x1 x2)
        (AdSq.adSquare (Ad.adMatrix x0 x1 x2)))
      (JVar.principalLogAdMatrix
        c1 c2AtZero zeroAd zeroAdSquare)) column
  ≤ sourcePrincipalLogColumnBound
sourcePrincipalLogVariationColumn c1 c2 x0 x1 x2 dataSet =
  Local.principalLogLocalLipschitzColumn
    c1 c2 c2AtZero
    x0 x1 x2 0ℚ 0ℚ 0ℚ
    sourceRadius sourceRadius sourceCoefficientLipschitz
    (asLocalModulusData c1 c2 x0 x1 x2 dataSet)

sourcePrincipalLogResidualColumnQuarter :
  ∀ c1 c2 x0 x1 x2 →
  SourceRadiusPrincipalLogData c1 c2 x0 x1 x2 →
  ∀ column →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    (Component.logJacobianResidual
      (JVar.principalLogAdMatrix
        c1 c2
        (Ad.adMatrix x0 x1 x2)
        (AdSq.adSquare (Ad.adMatrix x0 x1 x2)))) column
  ≤ Quarter.oneQuarter
sourcePrincipalLogResidualColumnQuarter c1 c2 x0 x1 x2 dataSet column =
  let
    current = JVar.principalLogAdMatrix
      c1 c2
      (Ad.adMatrix x0 x1 x2)
      (AdSq.adSquare (Ad.adMatrix x0 x1 x2))
    zero = JVar.principalLogAdMatrix c1 c2AtZero zeroAd zeroAdSquare

    raw = sourcePrincipalLogVariationColumn c1 c2 x0 x1 x2 dataSet column

    identify :
      RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (Variation.matrixDifference current zero) column
      ≡ RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (Component.logJacobianResidual current) column
    identify = Sums.sumRationalCong Physical.lieCoordinates3 _ _
      (λ row → cong ∣_∣
        (subst
          (λ reference →
            current row column - reference
            ≡ current row column - Jacobian.identity3 row column)
          (principalLogAtZeroIsIdentity c1 row column)
          refl))
  in
  ℚP.≤-trans
    (subst
      (λ lower → lower ≤ sourcePrincipalLogColumnBound)
      identify raw)
    sourcePrincipalLogColumnFitsQuarter

cmp109PrincipalLogSourceRadiusMatrixBoundLevel : ProofLevel
cmp109PrincipalLogSourceRadiusMatrixBoundLevel = machineChecked

cmp109PrincipalLogSourceRadiusQuarterLevel : ProofLevel
cmp109PrincipalLogSourceRadiusQuarterLevel = machineChecked

-- Remaining analytic bridge: instantiate the actual inverse-dexp c2 coefficient
-- with the Bishop endpoint modulus on |Y|<=1/12.  The rational budget required
-- here is exactly 1/14400.
cmp109PrincipalLogSourceRadiusBishopCoefficientLevel : ProofLevel
cmp109PrincipalLogSourceRadiusBishopCoefficientLevel = conditional
