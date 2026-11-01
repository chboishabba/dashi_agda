module DASHI.Physics.YangMills.BalabanCMP109FederbushPrimitiveDefectsToNormalizedInverseExact where

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
-- Put the Federbush conditioning theorem at its shortest physical boundary.
-- A caller supplies only
--
--   col(J_j-I) <= rho/8,
--   col(T_j-I) <= rho/4,
--
-- together with normalized contour weights.  The separate transport norm is
-- derived from T=I+(T-I), then the existing exact telescope gives
--
--   col(J_j T_j-I) <= 1/4.
--
-- Normalized averaging therefore yields an l1 quarter contraction and the
-- determinant-free inverse estimate ||x||_1 <= (4/3)||y||_1.
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
import DASHI.Physics.YangMills.BalabanCMP109FederbushLogTransportToNormalizedInverseExact as Existing
import DASHI.Physics.YangMills.BalabanCMP109FederbushTransportResidualControlsNormExact as TransportNorm
import DASHI.Physics.YangMills.BalabanCMP109FederbushQuarterReopeningExact as Quarter
import DASHI.Physics.YangMills.BalabanP33CMP109LocalLeafCalibrationExact as Calibration

record FederbushPrimitiveDefectData (Index : Set) : Set₁ where
  field
    indices : List Index
    weight : ℚ
    jacobian transport : Index → Jacobian.Lie3Matrix

    weightNonnegative : 0ℚ ≤ weight
    normalizedWeight :
      weight * Fibre.natAsRational (length indices)
      ≡ Data.Rational.Base.1ℚ

    logarithmResidualColumns : ∀ index column →
      RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (Component.logJacobianResidual (jacobian index)) column
      ≤ Calibration.logarithmAllocation

    transportResidualColumns : ∀ index column →
      RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (Component.transportResidual (transport index)) column
      ≤ Calibration.transportAllocation

open FederbushPrimitiveDefectData public

asPhysicalLogTransportData :
  ∀ {Index} → FederbushPrimitiveDefectData Index →
  Existing.FederbushPhysicalLogTransportData Index
asPhysicalLogTransportData dataSet = record
  { Existing.FederbushPhysicalLogTransportData.indices = indices dataSet
  ; Existing.FederbushPhysicalLogTransportData.weight = weight dataSet
  ; Existing.FederbushPhysicalLogTransportData.jacobian = jacobian dataSet
  ; Existing.FederbushPhysicalLogTransportData.transport = transport dataSet
  ; Existing.FederbushPhysicalLogTransportData.weightNonnegative =
      weightNonnegative dataSet
  ; Existing.FederbushPhysicalLogTransportData.normalizedWeight =
      normalizedWeight dataSet
  ; Existing.FederbushPhysicalLogTransportData.logarithmResidualColumns =
      logarithmResidualColumns dataSet
  ; Existing.FederbushPhysicalLogTransportData.transportColumns =
      λ index column →
        TransportNorm.calibratedTransportColumnBelowThree
          (transport dataSet index) column
          (transportResidualColumns dataSet index column)
  ; Existing.FederbushPhysicalLogTransportData.transportResidualColumns =
      transportResidualColumns dataSet
  }

primitiveDefectsGiveLocalQuarter :
  ∀ {Index} (dataSet : FederbushPrimitiveDefectData Index) index column →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    (Existing.physicalComponentResidual (asPhysicalLogTransportData dataSet) index)
    column
  ≤ Quarter.oneQuarter
primitiveDefectsGiveLocalQuarter dataSet =
  Existing.physicalComponentResidualColumnQuarter
    (asPhysicalLogTransportData dataSet)

primitiveDefectsNormalizedResidualL1Quarter :
  ∀ {Index} (dataSet : FederbushPrimitiveDefectData Index) vector →
  L1.vectorL1 Physical.lieCoordinates3
    (Existing.physicalNormalizedResidualAction
      (asPhysicalLogTransportData dataSet) vector)
  ≤ Quarter.oneQuarter * L1.vectorL1 Physical.lieCoordinates3 vector
primitiveDefectsNormalizedResidualL1Quarter dataSet =
  Existing.physicalNormalizedResidualL1Quarter
    (asPhysicalLogTransportData dataSet)

primitiveDefectsFederbushEquation :
  ∀ {Index} → FederbushPrimitiveDefectData Index →
  Jacobian.Lie3Vector → Jacobian.Lie3Vector → Set
primitiveDefectsFederbushEquation dataSet =
  Existing.physicalNormalizedFederbushEquation
    (asPhysicalLogTransportData dataSet)

primitiveDefectsGiveInverseFourThirds :
  ∀ {Index} (dataSet : FederbushPrimitiveDefectData Index)
    solution source →
  primitiveDefectsFederbushEquation dataSet solution source →
  L1.vectorL1 Physical.lieCoordinates3 solution
  ≤ Quarter.fourThirds * L1.vectorL1 Physical.lieCoordinates3 source
primitiveDefectsGiveInverseFourThirds dataSet =
  Existing.physicalNormalizedFederbushInverseFourThirds
    (asPhysicalLogTransportData dataSet)

primitiveDefectsGiveKernelTrivial :
  ∀ {Index} (dataSet : FederbushPrimitiveDefectData Index) solution →
  primitiveDefectsFederbushEquation dataSet solution Reopen.zeroVector →
  ∀ coordinate → solution coordinate ≡ 0ℚ
primitiveDefectsGiveKernelTrivial dataSet =
  Existing.physicalNormalizedFederbushKernelTrivial
    (asPhysicalLogTransportData dataSet)

cmp109FederbushPrimitiveDefectsToQuarterLevel : ProofLevel
cmp109FederbushPrimitiveDefectsToQuarterLevel = machineChecked

cmp109FederbushPrimitiveDefectsToInverseLevel : ProofLevel
cmp109FederbushPrimitiveDefectsToInverseLevel = machineChecked

-- Exact physical frontier for this segment: prove the principal-log and centre
-- adjoint-transport DEFECT column bounds on the selected CMP109 chart.
physicalCMP109FederbushPrimitiveDefectBoundsLevel : ProofLevel
physicalCMP109FederbushPrimitiveDefectBoundsLevel = conditional
