module DASHI.Physics.YangMills.BalabanCMP109FederbushCoefficientChartToInverseExact where

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
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University (2022), arXiv:2205.08354.
-- No DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Collapse the G1 inverse-conditioning lane to scalar coefficient and physical
-- chart data.  For each contour atom:
--
--   * J_j is the literal ad-polynomial inverse-dexp/principal-log matrix;
--   * T_j is the literal Ad_{U_j V^-1} centre transport;
--   * the principal-log matrix defect is derived from the endpoint coefficient
--     modulus, rather than supplied as a matrix hypothesis;
--   * the transport defect is derived from the identity-chart chord theorem.
--
-- The normalized Federbush equation therefore has the checked 4/3 inverse once
-- these scalar/chord inputs are provided.  No anonymous 3x3 residual bound
-- remains in this path.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.List.Base using (length)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteFibreAverageExact as Fibre
import DASHI.Physics.YangMills.BalabanFiniteMatrixL1ContractionExact as L1
import DASHI.Physics.YangMills.BalabanFiniteStrictContractionReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedJacobianExact as Jacobian
import DASHI.Physics.YangMills.BalabanCMP109FederbushTransportDefectFromIdentityChartExact as TransportChart
import DASHI.Physics.YangMills.BalabanCMP109FederbushPhysicalChartToNormalizedInverseExact as PhysicalChart
import DASHI.Physics.YangMills.BalabanCMP109PrincipalLogDefectFromEndpointModulusExact as Log
import DASHI.Physics.YangMills.BalabanCMP109SU2AdCoordinateMassExact as Ad
import DASHI.Physics.YangMills.BalabanCMP109SU2AdSquareVariationMassExact as AdSq
import DASHI.Physics.YangMills.BalabanCMP109SU2PrincipalLogAdPolynomialVariationMassExact as JVar
import DASHI.Physics.YangMills.BalabanCMP109FederbushQuarterReopeningExact as Quarter

record FederbushCoefficientChartData (Index : Set) : Set₁ where
  field
    indices : List Index
    weight : ℚ

    input centre : Index → Q.RationalQuaternion
    c1 c2 : Index → ℚ
    x0 x1 x2 : Index → ℚ

    weightNonnegative : 0ℚ ≤ weight
    normalizedWeight :
      weight * Fibre.natAsRational (length indices) ≡ 1ℚ

    transportIdentityChart : ∀ index →
      TransportChart.IdentityChartTransportData
        (input index) (centre index)

    principalLogEndpoint : ∀ index →
      Log.PrincipalLogEndpointData
        (c1 index) (c2 index)
        (x0 index) (x1 index) (x2 index)

open FederbushCoefficientChartData public

principalLogMatrix :
  ∀ {Index} → FederbushCoefficientChartData Index →
  Index → Jacobian.Lie3Matrix
principalLogMatrix dataSet index =
  JVar.principalLogAdMatrix
    (c1 dataSet index)
    (c2 dataSet index)
    (Ad.adMatrix
      (x0 dataSet index) (x1 dataSet index) (x2 dataSet index))
    (AdSq.adSquare
      (Ad.adMatrix
        (x0 dataSet index) (x1 dataSet index) (x2 dataSet index)))

asPhysicalChartData :
  ∀ {Index} → FederbushCoefficientChartData Index →
  PhysicalChart.FederbushPhysicalChartData Index
asPhysicalChartData dataSet = record
  { PhysicalChart.FederbushPhysicalChartData.indices = indices dataSet
  ; PhysicalChart.FederbushPhysicalChartData.weight = weight dataSet
  ; PhysicalChart.FederbushPhysicalChartData.input = input dataSet
  ; PhysicalChart.FederbushPhysicalChartData.centre = centre dataSet
  ; PhysicalChart.FederbushPhysicalChartData.principalLogJacobian =
      principalLogMatrix dataSet
  ; PhysicalChart.FederbushPhysicalChartData.weightNonnegative =
      weightNonnegative dataSet
  ; PhysicalChart.FederbushPhysicalChartData.normalizedWeight =
      normalizedWeight dataSet
  ; PhysicalChart.FederbushPhysicalChartData.identityChart =
      transportIdentityChart dataSet
  ; PhysicalChart.FederbushPhysicalChartData.principalLogResidualColumns =
      λ index column →
        Log.principalLogResidualColumnWithinAllocation
          (c1 dataSet index)
          (c2 dataSet index)
          (x0 dataSet index)
          (x1 dataSet index)
          (x2 dataSet index)
          (principalLogEndpoint dataSet index)
          column
  }

coefficientChartFederbushEquation :
  ∀ {Index} → FederbushCoefficientChartData Index →
  Jacobian.Lie3Vector → Jacobian.Lie3Vector → Set
coefficientChartFederbushEquation dataSet =
  PhysicalChart.physicalChartFederbushEquation (asPhysicalChartData dataSet)

coefficientChartInverseFourThirds :
  ∀ {Index} (dataSet : FederbushCoefficientChartData Index)
    solution source →
  coefficientChartFederbushEquation dataSet solution source →
  L1.vectorL1 Physical.lieCoordinates3 solution
  ≤ Quarter.fourThirds * L1.vectorL1 Physical.lieCoordinates3 source
coefficientChartInverseFourThirds dataSet =
  PhysicalChart.physicalChartInverseFourThirds (asPhysicalChartData dataSet)

coefficientChartKernelTrivial :
  ∀ {Index} (dataSet : FederbushCoefficientChartData Index) solution →
  coefficientChartFederbushEquation dataSet solution Reopen.zeroVector →
  ∀ coordinate → solution coordinate ≡ 0ℚ
coefficientChartKernelTrivial dataSet =
  PhysicalChart.physicalChartKernelTrivial (asPhysicalChartData dataSet)

cmp109FederbushCoefficientChartToInverseLevel : ProofLevel
cmp109FederbushCoefficientChartToInverseLevel = machineChecked

-- The remaining G1 conditioning boundary is now scalar/source-geometric:
--   * the selected quaternion identity-chart chord budget;
--   * the actual inverse-dexp coefficient endpoint modulus and coordinate cube.
-- The Bishop coefficient development already proves the stronger analytic
-- endpoint modulus; its exact concrete-real -> rational instantiation remains.
physicalCMP109FederbushCoefficientAndChordInputsLevel : ProofLevel
physicalCMP109FederbushCoefficientAndChordInputsLevel = conditional
