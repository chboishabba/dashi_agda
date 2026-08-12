module DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedResidualReopeningExact where

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
-- Finish the finite conditioning argument after writing the normalized
-- Federbush Jacobian as
--
--      Abar = I + R_F,
--      R_F = w sum_j R_j,       w |J| = 1.
--
-- If each local residual R_j has absolute column mass at most 1/4, normalized
-- averaging preserves that column mass exactly.  The repository's finite l1
-- theorem then gives
--
--      ||R_F v||_1 <= (1/4)||v||_1.
--
-- Consequently every solution of Abar x = y obeys
--
--      ||x||_1 <= (4/3)||y||_1,
--
-- and the homogeneous kernel is pointwise trivial on the explicit three-Lie-
-- coordinate selector.  This is a determinant-free inverse theorem; only the
-- physical local R_j mass producer remains to be connected to J_j T_j-I.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.List.Base using (length)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteFibreAverageExact as Fibre
import DASHI.Physics.YangMills.BalabanFiniteNormalizedKernelSchurExact as Normalized
import DASHI.Physics.YangMills.BalabanFiniteRectangularSchurSquaredExact as RectSchur
import DASHI.Physics.YangMills.BalabanFiniteMatrixL1ContractionExact as L1
import DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedJacobianExact as Jacobian
import DASHI.Physics.YangMills.BalabanCMP109FederbushQuarterReopeningExact as Quarter
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis

normalizedResidualAsKernel :
  ∀ {Index : Set} → ℚ → List Index →
  (Index → Jacobian.Lie3Matrix) → Jacobian.Lie3Matrix
normalizedResidualAsKernel weight indices residual =
  Normalized.normalizedKernel weight indices residual

normalizedResidualMatchesFederbush :
  ∀ {Index : Set} weight (indices : List Index) residual row column →
  normalizedResidualAsKernel weight indices residual row column
  ≡ Jacobian.normalizedFederbushResidual weight indices residual row column
normalizedResidualMatchesFederbush weight indices residual row column = refl

record FederbushQuarterResidualData (Index : Set) : Set₁ where
  field
    indices : List Index
    weight : ℚ
    residual : Index → Jacobian.Lie3Matrix

    weightNonnegative : 0ℚ ≤ weight
    normalizedWeight :
      weight * Fibre.natAsRational (length indices) ≡ 1ℚ

    localColumnQuarter : ∀ index column →
      RectSchur.rectAbsoluteColumnMass
        Physical.lieCoordinates3 (residual index) column
      ≤ Quarter.oneQuarter

open FederbushQuarterResidualData public

normalizedResidualColumnQuarter :
  ∀ {Index} (dataSet : FederbushQuarterResidualData Index) column →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    (normalizedResidualAsKernel
      (weight dataSet) (indices dataSet) (residual dataSet)) column
  ≤ Quarter.oneQuarter
normalizedResidualColumnQuarter dataSet column =
  Normalized.normalizedKernelColumnMassBound
    (weight dataSet)
    (indices dataSet)
    Physical.lieCoordinates3
    Physical.lieCoordinates3
    (residual dataSet)
    Quarter.oneQuarter
    column
    (weightNonnegative dataSet)
    (normalizedWeight dataSet)
    (λ index → localColumnQuarter dataSet index column)

normalizedResidualAction :
  ∀ {Index} → FederbushQuarterResidualData Index →
  Jacobian.Lie3Vector → Jacobian.Lie3Vector
normalizedResidualAction dataSet =
  L1.applyKernel Physical.lieCoordinates3
    (normalizedResidualAsKernel
      (weight dataSet) (indices dataSet) (residual dataSet))

normalizedResidualActionL1Quarter :
  ∀ {Index} (dataSet : FederbushQuarterResidualData Index) vector →
  L1.vectorL1 Physical.lieCoordinates3
      (normalizedResidualAction dataSet vector)
  ≤ Quarter.oneQuarter
      * L1.vectorL1 Physical.lieCoordinates3 vector
normalizedResidualActionL1Quarter dataSet vector =
  L1.applyKernelL1Bound
    Physical.lieCoordinates3
    (normalizedResidualAsKernel
      (weight dataSet) (indices dataSet) (residual dataSet))
    vector Quarter.oneQuarter
    (ℚP.nonNegative⁻¹ Quarter.oneQuarter)
    (λ column → normalizedResidualColumnQuarter dataSet column)

identityPlusNormalizedResidual :
  ∀ {Index} → FederbushQuarterResidualData Index →
  Jacobian.Lie3Vector → Jacobian.Lie3Vector
identityPlusNormalizedResidual dataSet vector row =
  vector row + normalizedResidualAction dataSet vector row

normalizedFederbushEquation :
  ∀ {Index} → FederbushQuarterResidualData Index →
  Jacobian.Lie3Vector → Jacobian.Lie3Vector → Set
normalizedFederbushEquation dataSet solution source =
  ∀ row → identityPlusNormalizedResidual dataSet solution row ≡ source row

normalizedFederbushSolutionL1FourThirds :
  ∀ {Index} (dataSet : FederbushQuarterResidualData Index)
    solution source →
  normalizedFederbushEquation dataSet solution source →
  L1.vectorL1 Physical.lieCoordinates3 solution
  ≤ Quarter.fourThirds * L1.vectorL1 Physical.lieCoordinates3 source
normalizedFederbushSolutionL1FourThirds dataSet solution source equation =
  Quarter.oneQuarterReopeningBound
    Physical.lieCoordinates3
    (normalizedResidualAction dataSet)
    solution source equation
    (normalizedResidualActionL1Quarter dataSet solution)

record Lie3Selector : Set₁ where
  field
    selector : Basis.FiniteSelector Physical.LieCoordinate3
    selectorElementsExact :
      Basis.elements selector ≡ Physical.lieCoordinates3

open Lie3Selector public

normalizedFederbushHomogeneousKernelTrivial :
  ∀ {Index} (dataSet : FederbushQuarterResidualData Index)
    (coordinates : Lie3Selector) solution →
  normalizedFederbushEquation dataSet solution (λ _ → 0ℚ) →
  ∀ coordinate → solution coordinate ≡ 0ℚ
normalizedFederbushHomogeneousKernelTrivial dataSet coordinates solution equation =
  let
    selectedEquation :
      Quarter.Reopen.IdentityPlusResidualEquation
        (normalizedResidualAction dataSet) solution Quarter.Reopen.zeroVector
    selectedEquation = equation

    selectedContraction :
      L1.vectorL1 (Basis.elements (selector coordinates))
        (normalizedResidualAction dataSet solution)
      ≤ Quarter.oneQuarter
        * L1.vectorL1 (Basis.elements (selector coordinates)) solution
    selectedContraction
      rewrite selectorElementsExact coordinates =
      normalizedResidualActionL1Quarter dataSet solution
  in
  Quarter.oneQuarterHomogeneousPointwiseZero
    (selector coordinates)
    (normalizedResidualAction dataSet)
    solution selectedEquation selectedContraction

cmp109FederbushNormalizedResidualColumnMassLevel : ProofLevel
cmp109FederbushNormalizedResidualColumnMassLevel = machineChecked

cmp109FederbushNormalizedResidualQuarterContractionLevel : ProofLevel
cmp109FederbushNormalizedResidualQuarterContractionLevel = machineChecked

cmp109FederbushNormalizedFourThirdsReopeningLevel : ProofLevel
cmp109FederbushNormalizedFourThirdsReopeningLevel = machineChecked

physicalCMP109FederbushLocalResidualMassProducerLevel : ProofLevel
physicalCMP109FederbushLocalResidualMassProducerLevel = conditional
