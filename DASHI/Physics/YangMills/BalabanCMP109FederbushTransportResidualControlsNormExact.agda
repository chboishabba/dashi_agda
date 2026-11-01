module DASHI.Physics.YangMills.BalabanCMP109FederbushTransportResidualControlsNormExact where

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
-- Remove an unnecessary independent hypothesis from the determinant-free
-- Federbush inverse lane.  The centre transport is already written as
--
--       T = I + (T-I).
--
-- On the literal three-coordinate su(2) carrier every identity column has l1
-- mass exactly one.  Therefore
--
--       col(T) <= 1 + col(T-I).
--
-- At the calibrated transport defect col(T-I) <= rho/4, rho=1/8192, this is
-- far below the coarse transport norm 3 used by the JT-I telescope.  Hence the
-- caller only has to prove the physical transport DEFECT bound; the separate
-- col(T)<=3 assumption is derived here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; _+_; _≤_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteRectangularSchurSquaredExact as RectSchur
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedJacobianExact as Jacobian
import DASHI.Physics.YangMills.BalabanCMP109FederbushComponentResidualExact as Component
import DASHI.Physics.YangMills.BalabanCMP109SU2PrincipalLogAdPolynomialVariationMassExact as MatrixMass
import DASHI.Physics.YangMills.BalabanCMP109FederbushResidualMassTelescopeExact as Mass
import DASHI.Physics.YangMills.BalabanP33CMP109LocalLeafCalibrationExact as Calibration
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

identityColumnMassExact : ∀ column →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    Jacobian.identity3 column
  ≡ 1ℚ
identityColumnMassExact Physical.coordinateX = refl
identityColumnMassExact Physical.coordinateY = refl
identityColumnMassExact Physical.coordinateZ = refl

transportColumnMassBelowIdentityPlusResidual :
  ∀ transport column defectBound →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
      (Component.transportResidual transport) column
    ≤ defectBound →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3 transport column
    ≤ 1ℚ + defectBound
transportColumnMassBelowIdentityPlusResidual transport column defectBound defect =
  let
    transportAsSum :
      RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3 transport column
      ≡ RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
          (MatrixMass.matrixAdd Jacobian.identity3
            (Component.transportResidual transport)) column
    transportAsSum =
      Sums.sumRationalCong Physical.lieCoordinates3 _ _
        (λ row → cong ∣_∣
          (Component.transportIsIdentityPlusResidual transport row column))

    sumBound = MatrixMass.matrixAddColumnMassBound
      Jacobian.identity3
      (Component.transportResidual transport)
      1ℚ defectBound column
      (subst
        (λ value → value ≤ 1ℚ)
        (sym (identityColumnMassExact column))
        ℚP.≤-refl)
      defect
  in
  subst
    (λ lower → lower ≤ 1ℚ + defectBound)
    (sym transportAsSum)
    sumBound

onePlusCalibratedTransportDefectBelowThree :
  1ℚ + Calibration.transportAllocation ≤ Mass.three
onePlusCalibratedTransportDefectBelowThree =
  Norm.nonnegativeDifferenceImpliesBelow
    (ℚP.nonNegative⁻¹
      (Mass.three - (1ℚ + Calibration.transportAllocation)))
  where
  open import Data.Rational.Base using (_-_)

calibratedTransportColumnBelowThree :
  ∀ transport column →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
      (Component.transportResidual transport) column
    ≤ Calibration.transportAllocation →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3 transport column
    ≤ Mass.three
calibratedTransportColumnBelowThree transport column defect =
  ℚP.≤-trans
    (transportColumnMassBelowIdentityPlusResidual
      transport column Calibration.transportAllocation defect)
    onePlusCalibratedTransportDefectBelowThree

cmp109FederbushIdentityColumnMassLevel : ProofLevel
cmp109FederbushIdentityColumnMassLevel = machineChecked

cmp109FederbushTransportDefectControlsNormLevel : ProofLevel
cmp109FederbushTransportDefectControlsNormLevel = machineChecked
