module DASHI.Physics.YangMills.BalabanCMP109FederbushTransportDefectFromIdentityChartExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- Specialize the checked two-background centre-transport theorem to the
-- identity reference pair.  Since
--
--       T(U,V) = Ad_{U V^-1},       T(1,1) = I,
--
-- the existing column estimate
--
--       col(T(U,V)-T(U',V')) <= 9 delta
--
-- gives a literal transport DEFECT estimate whenever
--
--       N(U-1)+N(V-1) <= delta^2.
--
-- At delta = rho/96, 9 delta <= 24 delta = rho/4, exactly the calibrated
-- transport allocation.  Thus this removes another anonymous physical matrix
-- bound: the remaining input is only the source-chart quaternion chord bound.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _*_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteRectangularSchurSquaredExact as RectSchur
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedJacobianExact as Jacobian
import DASHI.Physics.YangMills.BalabanCMP109FederbushComponentResidualExact as Component
import DASHI.Physics.YangMills.BalabanCMP109FederbushCentreTransportMatrixExact as Matrix
import DASHI.Physics.YangMills.BalabanCMP109FederbushCentreTransportColumnMassExact as Column
import DASHI.Physics.YangMills.BalabanCMP109FederbushComponentVariationExact as Variation
import DASHI.Physics.YangMills.BalabanP33CMP109LocalLeafCalibrationExact as Calibration

identityTransportEntryExact : ∀ row column →
  Matrix.centreTransportMatrix Q.oneQ Q.oneQ row column
  ≡ Jacobian.identity3 row column
identityTransportEntryExact Physical.coordinateX Physical.coordinateX = refl
identityTransportEntryExact Physical.coordinateX Physical.coordinateY = refl
identityTransportEntryExact Physical.coordinateX Physical.coordinateZ = refl
identityTransportEntryExact Physical.coordinateY Physical.coordinateX = refl
identityTransportEntryExact Physical.coordinateY Physical.coordinateY = refl
identityTransportEntryExact Physical.coordinateY Physical.coordinateZ = refl
identityTransportEntryExact Physical.coordinateZ Physical.coordinateX = refl
identityTransportEntryExact Physical.coordinateZ Physical.coordinateY = refl
identityTransportEntryExact Physical.coordinateZ Physical.coordinateZ = refl

transportDifferenceAgainstIdentityIsResidual : ∀ input centre row column →
  Variation.matrixDifference
    (Matrix.centreTransportMatrix input centre)
    (Matrix.centreTransportMatrix Q.oneQ Q.oneQ) row column
  ≡ Component.transportResidual
      (Matrix.centreTransportMatrix input centre) row column
transportDifferenceAgainstIdentityIsResidual input centre row column =
  subst
    (λ reference →
      Matrix.centreTransportMatrix input centre row column - reference
      ≡ Matrix.centreTransportMatrix input centre row column
          - Jacobian.identity3 row column)
    (identityTransportEntryExact row column)
    refl
  where
  open import Data.Rational.Base using (_-_)

identityQuaternionUnit : Norm.normSq Q.oneQ ≡ 1ℚ
identityQuaternionUnit = refl

record IdentityChartTransportData
    (input centre : Q.RationalQuaternion) : Set where
  field
    inputUnit : Norm.normSq input ≡ 1ℚ
    centreUnit : Norm.normSq centre ≡ 1ℚ
    chartDifferenceSquare :
      Norm.normSq (DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact._-q_ input Q.oneQ)
        + Norm.normSq (DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact._-q_ centre Q.oneQ)
      ≤ Calibration.transportStepRadius * Calibration.transportStepRadius

open IdentityChartTransportData public

asCentreTransportChartPair :
  ∀ input centre → IdentityChartTransportData input centre →
  Column.CentreTransportChartPair
    input centre Q.oneQ Q.oneQ Calibration.transportStepRadius
asCentreTransportChartPair input centre dataSet = record
  { Column.CentreTransportChartPair.deltaPositive =
      ℚP.positive⁻¹ Calibration.transportStepRadius
  ; Column.CentreTransportChartPair.uUnit = inputUnit dataSet
  ; Column.CentreTransportChartPair.vUnit = centreUnit dataSet
  ; Column.CentreTransportChartPair.u'Unit = identityQuaternionUnit
  ; Column.CentreTransportChartPair.v'Unit = identityQuaternionUnit
  ; Column.CentreTransportChartPair.pairDifferenceSquare =
      chartDifferenceSquare dataSet
  }

nineTransportStepsFitAllocation :
  Column.nine * Calibration.transportStepRadius
  ≤ Calibration.transportAllocation
nineTransportStepsFitAllocation =
  Norm.nonnegativeDifferenceImpliesBelow
    (ℚP.nonNegative⁻¹
      (Calibration.transportAllocation
        - Column.nine * Calibration.transportStepRadius))
  where
  open import Data.Rational.Base using (_-_)

transportResidualColumnWithinAllocation :
  ∀ input centre → IdentityChartTransportData input centre →
  ∀ column →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    (Component.transportResidual
      (Matrix.centreTransportMatrix input centre)) column
  ≤ Calibration.transportAllocation
transportResidualColumnWithinAllocation input centre dataSet column =
  let
    raw = Column.transportMatrixColumnMassBound
      input centre Q.oneQ Q.oneQ Calibration.transportStepRadius
      (asCentreTransportChartPair input centre dataSet)
      column

    identify :
      RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (Variation.matrixDifference
          (Matrix.centreTransportMatrix input centre)
          (Matrix.centreTransportMatrix Q.oneQ Q.oneQ)) column
      ≡ RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (Component.transportResidual
          (Matrix.centreTransportMatrix input centre)) column
    identify = Sums.sumRationalCong Physical.lieCoordinates3 _ _
      (λ row → cong ∣_∣
        (transportDifferenceAgainstIdentityIsResidual
          input centre row column))
  in
  ℚP.≤-trans
    (subst
      (λ lower → lower ≤ Column.nine * Calibration.transportStepRadius)
      identify raw)
    nineTransportStepsFitAllocation

cmp109FederbushIdentityTransportLevel : ProofLevel
cmp109FederbushIdentityTransportLevel = machineChecked

cmp109FederbushTransportDefectFromIdentityChartLevel : ProofLevel
cmp109FederbushTransportDefectFromIdentityChartLevel = machineChecked

-- Remaining physical leaf for this half of G1: show the selected input and
-- Federbush centre, after the common reference trivialization, satisfy the
-- calibrated squared chord budget against the identity pair.
physicalCMP109FederbushIdentityChartChordLevel : ProofLevel
physicalCMP109FederbushIdentityChartChordLevel = conditional
