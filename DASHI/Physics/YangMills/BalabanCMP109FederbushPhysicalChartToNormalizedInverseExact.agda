module DASHI.Physics.YangMills.BalabanCMP109FederbushPhysicalChartToNormalizedInverseExact where

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
-- Make the determinant-free Federbush inverse consume the literal physical
-- centre transport, not an arbitrary 3x3 matrix.  For every contour atom the
-- transport is definitionally
--
--       T_j = Ad_{U_j V^-1}.
--
-- The selected identity-chart chord estimate gives col(T_j-I)<=rho/4; the only
-- other local matrix input is the principal-log differential defect
-- col(J_j-I)<=rho/8.  The checked primitive-defect theorem then yields the
-- normalized quarter contraction and 4/3 inverse bound.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.List.Base using (length)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteFibreAverageExact as Fibre
import DASHI.Physics.YangMills.BalabanFiniteRectangularSchurSquaredExact as RectSchur
import DASHI.Physics.YangMills.BalabanFiniteMatrixL1ContractionExact as L1
import DASHI.Physics.YangMills.BalabanFiniteStrictContractionReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedJacobianExact as Jacobian
import DASHI.Physics.YangMills.BalabanCMP109FederbushComponentResidualExact as Component
import DASHI.Physics.YangMills.BalabanCMP109FederbushCentreTransportMatrixExact as Matrix
import DASHI.Physics.YangMills.BalabanCMP109FederbushTransportDefectFromIdentityChartExact as Chart
import DASHI.Physics.YangMills.BalabanCMP109FederbushPrimitiveDefectsToNormalizedInverseExact as Primitive
import DASHI.Physics.YangMills.BalabanCMP109FederbushLogTransportToNormalizedInverseExact as Existing
import DASHI.Physics.YangMills.BalabanCMP109FederbushQuarterReopeningExact as Quarter
import DASHI.Physics.YangMills.BalabanP33CMP109LocalLeafCalibrationExact as Calibration

record FederbushPhysicalChartData (Index : Set) : Set₁ where
  field
    indices : List Index
    weight : ℚ

    input centre : Index → Q.RationalQuaternion
    principalLogJacobian : Index → Jacobian.Lie3Matrix

    weightNonnegative : 0ℚ ≤ weight
    normalizedWeight :
      weight * Fibre.natAsRational (length indices) ≡ 1ℚ

    identityChart : ∀ index →
      Chart.IdentityChartTransportData (input index) (centre index)

    principalLogResidualColumns : ∀ index column →
      RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (Component.logJacobianResidual (principalLogJacobian index)) column
      ≤ Calibration.logarithmAllocation

open FederbushPhysicalChartData public

physicalTransport :
  ∀ {Index} → FederbushPhysicalChartData Index →
  Index → Jacobian.Lie3Matrix
physicalTransport dataSet index =
  Matrix.centreTransportMatrix
    (input dataSet index) (centre dataSet index)

asPrimitiveDefectData :
  ∀ {Index} → FederbushPhysicalChartData Index →
  Primitive.FederbushPrimitiveDefectData Index
asPrimitiveDefectData dataSet = record
  { Primitive.FederbushPrimitiveDefectData.indices = indices dataSet
  ; Primitive.FederbushPrimitiveDefectData.weight = weight dataSet
  ; Primitive.FederbushPrimitiveDefectData.jacobian =
      principalLogJacobian dataSet
  ; Primitive.FederbushPrimitiveDefectData.transport = physicalTransport dataSet
  ; Primitive.FederbushPrimitiveDefectData.weightNonnegative =
      weightNonnegative dataSet
  ; Primitive.FederbushPrimitiveDefectData.normalizedWeight =
      normalizedWeight dataSet
  ; Primitive.FederbushPrimitiveDefectData.logarithmResidualColumns =
      principalLogResidualColumns dataSet
  ; Primitive.FederbushPrimitiveDefectData.transportResidualColumns =
      λ index column →
        Chart.transportResidualColumnWithinAllocation
          (input dataSet index)
          (centre dataSet index)
          (identityChart dataSet index)
          column
  }

physicalChartNormalizedResidualL1Quarter :
  ∀ {Index} (dataSet : FederbushPhysicalChartData Index) vector →
  L1.vectorL1 Physical.lieCoordinates3
    (Existing.physicalNormalizedResidualAction
      (Primitive.asPhysicalLogTransportData (asPrimitiveDefectData dataSet)) vector)
  ≤ Quarter.oneQuarter * L1.vectorL1 Physical.lieCoordinates3 vector
physicalChartNormalizedResidualL1Quarter dataSet =
  Primitive.primitiveDefectsNormalizedResidualL1Quarter
    (asPrimitiveDefectData dataSet)

physicalChartFederbushEquation :
  ∀ {Index} → FederbushPhysicalChartData Index →
  Jacobian.Lie3Vector → Jacobian.Lie3Vector → Set
physicalChartFederbushEquation dataSet =
  Primitive.primitiveDefectsFederbushEquation
    (asPrimitiveDefectData dataSet)

physicalChartInverseFourThirds :
  ∀ {Index} (dataSet : FederbushPhysicalChartData Index)
    solution source →
  physicalChartFederbushEquation dataSet solution source →
  L1.vectorL1 Physical.lieCoordinates3 solution
  ≤ Quarter.fourThirds * L1.vectorL1 Physical.lieCoordinates3 source
physicalChartInverseFourThirds dataSet =
  Primitive.primitiveDefectsGiveInverseFourThirds
    (asPrimitiveDefectData dataSet)

physicalChartKernelTrivial :
  ∀ {Index} (dataSet : FederbushPhysicalChartData Index) solution →
  physicalChartFederbushEquation dataSet solution Reopen.zeroVector →
  ∀ coordinate → solution coordinate ≡ 0ℚ
physicalChartKernelTrivial dataSet =
  Primitive.primitiveDefectsGiveKernelTrivial
    (asPrimitiveDefectData dataSet)

cmp109FederbushPhysicalTransportIdentificationLevel : ProofLevel
cmp109FederbushPhysicalTransportIdentificationLevel = machineChecked

cmp109FederbushPhysicalChartToInverseLevel : ProofLevel
cmp109FederbushPhysicalChartToInverseLevel = machineChecked

-- G1 conditioning now has only two local physical leaves:
--   (i) selected identity-chart chord control for U_j,V;
--  (ii) principal-log differential defect on that same selected chart.
physicalCMP109FederbushSelectedChartLeavesLevel : ProofLevel
physicalCMP109FederbushSelectedChartLeavesLevel = conditional
