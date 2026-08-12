module DASHI.Physics.YangMills.BalabanCMP109FederbushResidualMassTelescopeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Quantify the exact component telescope
--
--      JT-I = (J-I)T + (T-I)
--
-- directly in the finite l1 column mass used by the determinant-free
-- Federbush reopening.  If
--
--   col(J-I) <= l,   col(T) <= t,   col(T-I) <= s,
--
-- then
--
--   col(JT-I) <= l t + s.
--
-- At the source-calibrated leaves l=rho/8 and s=rho/4, the very coarse
-- three-coordinate transport bound t=3 already gives
--
--   col(JT-I) <= 5 rho / 8 = 5/65536 < 1/4.
--
-- Thus Federbush inversion has enormous margin and does not need a sharp
-- Euclidean-to-l1 transport conversion.  The remaining physical task is only
-- to identify the principal-log and transport matrices with these calibrated
-- local column bounds.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _/_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanFiniteRectangularSchurSquaredExact as RectSchur
import DASHI.Physics.YangMills.BalabanFiniteMatrixL1ContractionExact as L1
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedJacobianExact as Jacobian
import DASHI.Physics.YangMills.BalabanCMP109FederbushComponentResidualExact as Component
import DASHI.Physics.YangMills.BalabanCMP109FederbushQuarterReopeningExact as Quarter
import DASHI.Physics.YangMills.BalabanP33CMP109LocalLeafCalibrationExact as Calibration

matrixColumn : Jacobian.Lie3Matrix → Physical.LieCoordinate3 → Jacobian.Lie3Vector
matrixColumn matrix column row = matrix row column

composeColumnIsApply : ∀ outer inner column row →
  Component.matrixCompose outer inner row column
  ≡ L1.applyKernel Physical.lieCoordinates3 outer
      (matrixColumn inner column) row
composeColumnIsApply outer inner column row = refl

composeColumnMassBound :
  ∀ outer inner logBound transportBound column →
  0ℚ ≤ logBound →
  (∀ selected →
    RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3 outer selected
    ≤ logBound) →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3 inner column
    ≤ transportBound →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    (Component.matrixCompose outer inner) column
  ≤ logBound * transportBound
composeColumnMassBound outer inner logBound transportBound column
    logNonnegative outerColumns innerColumn =
  let
    action = L1.applyKernelL1Bound
      Physical.lieCoordinates3 outer (matrixColumn inner column)
      logBound logNonnegative outerColumns

    innerMeaning :
      L1.vectorL1 Physical.lieCoordinates3 (matrixColumn inner column)
      ≡ RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3 inner column
    innerMeaning = refl

    actionMeaning :
      L1.vectorL1 Physical.lieCoordinates3
        (L1.applyKernel Physical.lieCoordinates3 outer
          (matrixColumn inner column))
      ≡ RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
          (Component.matrixCompose outer inner) column
    actionMeaning = refl

    scaledInner = Norm.scaleNonnegative logBound logNonnegative innerColumn
  in
  ℚP.≤-trans
    (subst
      (λ lower → lower
        ≤ logBound
          * RectSchur.rectAbsoluteColumnMass
              Physical.lieCoordinates3 inner column)
      actionMeaning
      (subst
        (λ upper →
          L1.vectorL1 Physical.lieCoordinates3
            (L1.applyKernel Physical.lieCoordinates3 outer
              (matrixColumn inner column))
          ≤ logBound * upper)
        innerMeaning action))
    scaledInner

residualColumnTriangle : ∀ jacobian transport column →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
      (Component.componentResidual jacobian transport) column
  ≤ RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
      (Component.matrixCompose
        (Component.logJacobianResidual jacobian) transport) column
    + RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
      (Component.transportResidual transport) column
residualColumnTriangle jacobian transport column =
  Schur.sumPointwiseBelow Physical.lieCoordinates3 _ _
    (λ row →
      subst
        (λ value →
          ∣ value ∣
          ≤ ∣ Component.matrixCompose
                (Component.logJacobianResidual jacobian) transport row column ∣
            + ∣ Component.transportResidual transport row column ∣)
        (Component.componentResidualTelescopeExact
          jacobian transport row column)
        (ℚP.∣p+q∣≤∣p∣+∣q∣
          (Component.matrixCompose
            (Component.logJacobianResidual jacobian) transport row column)
          (Component.transportResidual transport row column)))

componentResidualColumnMassBound :
  ∀ jacobian transport logBound transportNormBound transportDefectBound column →
  0ℚ ≤ logBound →
  (∀ selected →
    RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
      (Component.logJacobianResidual jacobian) selected
    ≤ logBound) →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3 transport column
    ≤ transportNormBound →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
      (Component.transportResidual transport) column
    ≤ transportDefectBound →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
      (Component.componentResidual jacobian transport) column
  ≤ logBound * transportNormBound + transportDefectBound
componentResidualColumnMassBound
    jacobian transport logBound transportNormBound transportDefectBound column
    logNonnegative logColumns transportColumn transportDefectColumn =
  ℚP.≤-trans
    (residualColumnTriangle jacobian transport column)
    (ℚP.+-mono-≤
      (composeColumnMassBound
        (Component.logJacobianResidual jacobian) transport
        logBound transportNormBound column
        logNonnegative logColumns transportColumn)
      transportDefectColumn)

three : ℚ
three = + 3 / 1

selectedFederbushComponentResidualBudget : ℚ
selectedFederbushComponentResidualBudget = + 5 / 65536

selectedFederbushResidualBudgetExact :
  Calibration.logarithmAllocation * three
    + Calibration.transportAllocation
  ≡ selectedFederbushComponentResidualBudget
selectedFederbushResidualBudgetExact = ℚRing.solve []

selectedFederbushResidualFitsQuarter :
  selectedFederbushComponentResidualBudget ≤ Quarter.oneQuarter
selectedFederbushResidualFitsQuarter = ℚP.nonNegative⁻¹
  (Quarter.oneQuarter - selectedFederbushComponentResidualBudget)
  |>gap
  where
  infixl 0 _|>gap
  _|>gap :
    0ℚ ≤ Quarter.oneQuarter - selectedFederbushComponentResidualBudget →
    selectedFederbushComponentResidualBudget ≤ Quarter.oneQuarter
  _|>gap proof = Norm.nonnegativeDifferenceImpliesBelow proof

selectedComponentResidualColumnQuarter :
  ∀ jacobian transport column →
  (∀ selected →
    RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
      (Component.logJacobianResidual jacobian) selected
    ≤ Calibration.logarithmAllocation) →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3 transport column
    ≤ three →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
      (Component.transportResidual transport) column
    ≤ Calibration.transportAllocation →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
      (Component.componentResidual jacobian transport) column
    ≤ Quarter.oneQuarter
selectedComponentResidualColumnQuarter
    jacobian transport column logColumns transportColumn transportDefectColumn =
  let
    local = componentResidualColumnMassBound
      jacobian transport
      Calibration.logarithmAllocation three Calibration.transportAllocation column
      (ℚP.nonNegative⁻¹ Calibration.logarithmAllocation)
      logColumns transportColumn transportDefectColumn

    calibrated :
      RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (Component.componentResidual jacobian transport) column
      ≤ selectedFederbushComponentResidualBudget
    calibrated = subst
      (λ upper →
        RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
          (Component.componentResidual jacobian transport) column
        ≤ upper)
      selectedFederbushResidualBudgetExact local
  in
  ℚP.≤-trans calibrated selectedFederbushResidualFitsQuarter

cmp109FederbushResidualMassProductLevel : ProofLevel
cmp109FederbushResidualMassProductLevel = machineChecked

cmp109FederbushSelectedResidualQuarterArithmeticLevel : ProofLevel
cmp109FederbushSelectedResidualQuarterArithmeticLevel = machineChecked

physicalCMP109FederbushLogTransportColumnBoundsLevel : ProofLevel
physicalCMP109FederbushLogTransportColumnBoundsLevel = conditional
