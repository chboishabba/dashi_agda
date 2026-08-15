module DASHI.Physics.YangMills.BalabanCMP109FederbushLogTransportToNormalizedInverseExact where

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
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Remove the remaining synthetic "local residual producer" seam in the
-- determinant-free Federbush inverse lane.  The actual local inputs are the
-- two factor bounds already isolated from the source chart:
--
--   col(J_j-I) <= logarithmAllocation,
--   col(T_j)   <= 3,
--   col(T_j-I) <= transportAllocation.
--
-- The exact telescope JT-I=(J-I)T+(T-I) then gives col(JT-I)<=1/4.
-- Normalized contour averaging preserves this quarter bound, so the full
-- Federbush Jacobian is I+R_F with ||R_F||_{1->1}<=1/4 and hence has the
-- finite reopening estimate ||x||_1 <= (4/3)||y||_1.  No extra residual
-- hypothesis is requested from callers.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.List.Base using (length)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteFibreAverageExact as Fibre
import DASHI.Physics.YangMills.BalabanFiniteRectangularSchurSquaredExact as RectSchur
import DASHI.Physics.YangMills.BalabanFiniteMatrixL1ContractionExact as L1
import DASHI.Physics.YangMills.BalabanFiniteStrictContractionReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedJacobianExact as Jacobian
import DASHI.Physics.YangMills.BalabanCMP109FederbushComponentResidualExact as Component
import DASHI.Physics.YangMills.BalabanCMP109FederbushResidualMassTelescopeExact as Mass
import DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedResidualReopeningExact as Normalized
import DASHI.Physics.YangMills.BalabanCMP109FederbushQuarterReopeningExact as Quarter
import DASHI.Physics.YangMills.BalabanP33CMP109LocalLeafCalibrationExact as Calibration

record FederbushPhysicalLogTransportData (Index : Set) : Set₁ where
  field
    indices : List Index
    weight : ℚ
    jacobian transport : Index → Jacobian.Lie3Matrix

    weightNonnegative : 0ℚ ≤ weight
    normalizedWeight :
      weight * Fibre.natAsRational (length indices) ≡ Data.Rational.Base.1ℚ

    logarithmResidualColumns : ∀ index selected →
      RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (Component.logJacobianResidual (jacobian index)) selected
      ≤ Calibration.logarithmAllocation

    transportColumns : ∀ index column →
      RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (transport index) column
      ≤ Mass.three

    transportResidualColumns : ∀ index column →
      RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (Component.transportResidual (transport index)) column
      ≤ Calibration.transportAllocation

open FederbushPhysicalLogTransportData public

physicalComponentResidual :
  ∀ {Index} → FederbushPhysicalLogTransportData Index →
  Index → Jacobian.Lie3Matrix
physicalComponentResidual dataSet index =
  Component.componentResidual
    (jacobian dataSet index)
    (transport dataSet index)

physicalComponentResidualColumnQuarter :
  ∀ {Index} (dataSet : FederbushPhysicalLogTransportData Index)
    index column →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    (physicalComponentResidual dataSet index) column
  ≤ Quarter.oneQuarter
physicalComponentResidualColumnQuarter dataSet index column =
  Mass.selectedComponentResidualColumnQuarter
    (jacobian dataSet index)
    (transport dataSet index)
    column
    (logarithmResidualColumns dataSet index)
    (transportColumns dataSet index column)
    (transportResidualColumns dataSet index column)

asQuarterResidualData :
  ∀ {Index} → FederbushPhysicalLogTransportData Index →
  Normalized.FederbushQuarterResidualData Index
asQuarterResidualData dataSet = record
  { Normalized.FederbushQuarterResidualData.indices = indices dataSet
  ; Normalized.FederbushQuarterResidualData.weight = weight dataSet
  ; Normalized.FederbushQuarterResidualData.residual =
      physicalComponentResidual dataSet
  ; Normalized.FederbushQuarterResidualData.weightNonnegative =
      weightNonnegative dataSet
  ; Normalized.FederbushQuarterResidualData.normalizedWeight =
      normalizedWeight dataSet
  ; Normalized.FederbushQuarterResidualData.localColumnQuarter =
      physicalComponentResidualColumnQuarter dataSet
  }

physicalNormalizedResidualAction :
  ∀ {Index} → FederbushPhysicalLogTransportData Index →
  Jacobian.Lie3Vector → Jacobian.Lie3Vector
physicalNormalizedResidualAction dataSet =
  Normalized.normalizedResidualAction (asQuarterResidualData dataSet)

physicalNormalizedResidualL1Quarter :
  ∀ {Index} (dataSet : FederbushPhysicalLogTransportData Index) vector →
  L1.vectorL1 Physical.lieCoordinates3
    (physicalNormalizedResidualAction dataSet vector)
  ≤ Quarter.oneQuarter * L1.vectorL1 Physical.lieCoordinates3 vector
physicalNormalizedResidualL1Quarter dataSet =
  Normalized.normalizedResidualActionL1Quarter
    (asQuarterResidualData dataSet)

physicalNormalizedFederbushEquation :
  ∀ {Index} → FederbushPhysicalLogTransportData Index →
  Jacobian.Lie3Vector → Jacobian.Lie3Vector → Set
physicalNormalizedFederbushEquation dataSet =
  Normalized.normalizedFederbushEquation (asQuarterResidualData dataSet)

physicalNormalizedFederbushInverseFourThirds :
  ∀ {Index} (dataSet : FederbushPhysicalLogTransportData Index)
    solution source →
  physicalNormalizedFederbushEquation dataSet solution source →
  L1.vectorL1 Physical.lieCoordinates3 solution
  ≤ Quarter.fourThirds * L1.vectorL1 Physical.lieCoordinates3 source
physicalNormalizedFederbushInverseFourThirds dataSet =
  Normalized.normalizedFederbushSolutionL1FourThirds
    (asQuarterResidualData dataSet)

physicalNormalizedFederbushKernelTrivial :
  ∀ {Index} (dataSet : FederbushPhysicalLogTransportData Index) solution →
  physicalNormalizedFederbushEquation dataSet solution Reopen.zeroVector →
  ∀ coordinate → solution coordinate ≡ 0ℚ
physicalNormalizedFederbushKernelTrivial dataSet =
  Normalized.normalizedFederbushHomogeneousKernelTrivial
    (asQuarterResidualData dataSet)

cmp109FederbushLogTransportToLocalResidualLevel : ProofLevel
cmp109FederbushLogTransportToLocalResidualLevel = machineChecked

cmp109FederbushLogTransportToNormalizedInverseLevel : ProofLevel
cmp109FederbushLogTransportToNormalizedInverseLevel = machineChecked

-- This is now the actual physical leaf for the inverse-conditioning segment:
-- identify the source principal-log differential and centre transport with the
-- calibrated column bounds.  No independent residual-mass producer remains.
physicalCMP109FederbushLogTransportColumnBoundsLevel : ProofLevel
physicalCMP109FederbushLogTransportColumnBoundsLevel = conditional
