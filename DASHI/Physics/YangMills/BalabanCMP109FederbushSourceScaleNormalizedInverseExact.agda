module DASHI.Physics.YangMills.BalabanCMP109FederbushSourceScaleNormalizedInverseExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
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
-- Finish the determinant-free conditioning argument at the ACTUAL source
-- radius.  Each contour component supplies the two source-scale estimates
--
--   col(J_j-I) <= t/2+t^2/6,  t=1/12,
--   col(T_j-I) <= 1/6.
--
-- BalabanCMP109FederbushSourceScaleQuarterExact proves from these alone that
-- col(J_j T_j-I)<=1/4.  Normalized contour averaging preserves the quarter
-- column bound exactly, and the existing finite l1 reopening gives
--
--   ||x||_1 <= (4/3)||y||_1
--
-- plus trivial homogeneous kernel.  No determinant, Neumann series, rho/96
-- absolute chart, or independently supplied residual estimate is used.
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
import DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedJacobianExact as Jacobian
import DASHI.Physics.YangMills.BalabanCMP109FederbushComponentResidualExact as Component
import DASHI.Physics.YangMills.BalabanCMP109FederbushSourceScaleQuarterExact as SourceScale
import DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedResidualReopeningExact as Normalized
import DASHI.Physics.YangMills.BalabanCMP109FederbushQuarterReopeningExact as Quarter

record FederbushSourceScaleData (Index : Set) : Set₁ where
  field
    indices : List Index
    weight : ℚ
    jacobian transport : Index → Jacobian.Lie3Matrix

    weightNonnegative : 0ℚ ≤ weight
    normalizedWeight :
      weight * Fibre.natAsRational (length indices) ≡ 1ℚ

    principalLogColumns : ∀ index column →
      RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (Component.logJacobianResidual (jacobian index)) column
      ≤ SourceScale.sourceLogDefectBound

    transportDefectColumns : ∀ index column →
      RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (Component.transportResidual (transport index)) column
      ≤ SourceScale.sourceTransportDefectBound

open FederbushSourceScaleData public

sourceScaleComponentResidual :
  ∀ {Index} → FederbushSourceScaleData Index →
  Index → Jacobian.Lie3Matrix
sourceScaleComponentResidual dataSet index =
  Component.componentResidual
    (jacobian dataSet index) (transport dataSet index)

sourceScaleLocalQuarter :
  ∀ {Index} (dataSet : FederbushSourceScaleData Index) index column →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    (sourceScaleComponentResidual dataSet index) column
  ≤ Quarter.oneQuarter
sourceScaleLocalQuarter dataSet index column =
  SourceScale.sourceScaleComponentResidualQuarter
    (jacobian dataSet index) (transport dataSet index) column
    (principalLogColumns dataSet index)
    (transportDefectColumns dataSet index column)

asQuarterResidualData :
  ∀ {Index} → FederbushSourceScaleData Index →
  Normalized.FederbushQuarterResidualData Index
asQuarterResidualData dataSet = record
  { Normalized.FederbushQuarterResidualData.indices = indices dataSet
  ; Normalized.FederbushQuarterResidualData.weight = weight dataSet
  ; Normalized.FederbushQuarterResidualData.residual =
      sourceScaleComponentResidual dataSet
  ; Normalized.FederbushQuarterResidualData.weightNonnegative =
      weightNonnegative dataSet
  ; Normalized.FederbushQuarterResidualData.normalizedWeight =
      normalizedWeight dataSet
  ; Normalized.FederbushQuarterResidualData.localColumnQuarter =
      sourceScaleLocalQuarter dataSet
  }

sourceScaleFederbushEquation :
  ∀ {Index} → FederbushSourceScaleData Index →
  Jacobian.Lie3Vector → Jacobian.Lie3Vector → Set
sourceScaleFederbushEquation dataSet =
  Normalized.normalizedFederbushEquation (asQuarterResidualData dataSet)

sourceScaleNormalizedResidualL1Quarter :
  ∀ {Index} (dataSet : FederbushSourceScaleData Index) vector →
  L1.vectorL1 Physical.lieCoordinates3
    (Normalized.normalizedResidualAction (asQuarterResidualData dataSet) vector)
  ≤ Quarter.oneQuarter * L1.vectorL1 Physical.lieCoordinates3 vector
sourceScaleNormalizedResidualL1Quarter dataSet =
  Normalized.normalizedResidualActionL1Quarter (asQuarterResidualData dataSet)

sourceScaleInverseFourThirds :
  ∀ {Index} (dataSet : FederbushSourceScaleData Index)
    solution source →
  sourceScaleFederbushEquation dataSet solution source →
  L1.vectorL1 Physical.lieCoordinates3 solution
  ≤ Quarter.fourThirds * L1.vectorL1 Physical.lieCoordinates3 source
sourceScaleInverseFourThirds dataSet =
  Normalized.normalizedFederbushSolutionL1FourThirds
    (asQuarterResidualData dataSet)

sourceScaleKernelTrivial :
  ∀ {Index} (dataSet : FederbushSourceScaleData Index) solution →
  sourceScaleFederbushEquation dataSet solution Reopen.zeroVector →
  ∀ coordinate → solution coordinate ≡ 0ℚ
sourceScaleKernelTrivial dataSet =
  Normalized.normalizedFederbushHomogeneousKernelTrivial
    (asQuarterResidualData dataSet)

cmp109FederbushSourceScaleNormalizedQuarterLevel : ProofLevel
cmp109FederbushSourceScaleNormalizedQuarterLevel = machineChecked

cmp109FederbushSourceScaleFourThirdsInverseLevel : ProofLevel
cmp109FederbushSourceScaleFourThirdsInverseLevel = machineChecked

physicalCMP109FederbushSourceScaleMatrixBoundsLevel : ProofLevel
physicalCMP109FederbushSourceScaleMatrixBoundsLevel = conditional
