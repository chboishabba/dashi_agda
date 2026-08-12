module DASHI.Physics.YangMills.BalabanCMP109SelectedConstraintFixedPointResidualExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Wojciech Dybalski, Alexander Stottmeister, Yoh Tanimoto,
-- "The Balaban variational problem in the non-linear sigma model",
-- arXiv:2403.09800 (2024). No DOI recorded in the manuscript.
--
-- DASHI CONTRIBUTION
--
-- Close the fixed-point provenance hidden by a scalar little-o estimate.  The
-- selected normal correction is not an arbitrary vector c satisfying a bound:
-- it is the solution of the literal reopened equation
--
--        c + R(c) = r,
--
-- where r is the uncorrected constraint residual.  If the nonlinear normal
-- remainder obeys the already-budgeted quarter contraction
--
--        ||R(c)||_1 <= (1/4) ||c||_1,
--
-- the existing finite reopening theorem gives, for this SAME correction and
-- SAME residual,
--
--        ||c||_1 <= (4/3) ||r||_1.
--
-- This is the estimate needed on a kernel line: once Frechet differentiability
-- supplies ||r(th)|| = o(|t|), the actual normal fixed point is o(|t|) as well.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_; _<_; _/_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteMatrixL1ContractionExact as L1
import DASHI.Physics.YangMills.BalabanFiniteStrictContractionReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanCMP109FederbushQuarterReopeningExact as Quarter
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

record SelectedConstraintNormalFixedPoint (Index : Set) : Set₁ where
  field
    coordinates : List Index

    -- Literal residual C(A+v), after applying the fixed selected normal
    -- right-inverse convention used by the reopening equation.
    uncorrectedResidual : Reopen.Vector Index

    -- Nonlinear normal remainder in the same coordinates.
    normalRemainder : Reopen.Vector Index → Reopen.Vector Index

    -- The correction returned by the selected normal fixed-point solve.
    correction : Reopen.Vector Index

    -- This is the fixed-point equation itself, not an independent norm
    -- estimate on a separately supplied correction.
    correctionEquation :
      Reopen.IdentityPlusResidualEquation
        normalRemainder correction uncorrectedResidual

    quarterRemainderContraction :
      L1.vectorL1 coordinates (normalRemainder correction)
      ≤ Quarter.oneQuarter * L1.vectorL1 coordinates correction

open SelectedConstraintNormalFixedPoint public

selectedConstraintFixedPointResidualBound :
  ∀ {Index} (fixedPoint : SelectedConstraintNormalFixedPoint Index) →
  L1.vectorL1 (coordinates fixedPoint) (correction fixedPoint)
  ≤ Quarter.fourThirds
      * L1.vectorL1 (coordinates fixedPoint) (uncorrectedResidual fixedPoint)
selectedConstraintFixedPointResidualBound fixedPoint =
  Quarter.oneQuarterReopeningBound
    (coordinates fixedPoint)
    (normalRemainder fixedPoint)
    (correction fixedPoint)
    (uncorrectedResidual fixedPoint)
    (correctionEquation fixedPoint)
    (quarterRemainderContraction fixedPoint)

selectedConstraintQuarterContractionResidualBound =
  selectedConstraintFixedPointResidualBound

------------------------------------------------------------------------
-- Epsilon formulation of the kernel-line little-o transfer.
--
-- `timeMagnitude` is |t| and `directionScale` is the fixed norm of h.  The
-- analytic Frechet theorem supplies the residual estimate for arbitrarily small
-- epsilon.  This theorem proves that the selected fixed-point correction uses
-- exactly the same epsilon estimate enlarged only by 4/3.
------------------------------------------------------------------------

selectedConstraintKernelLineCorrectionLittleO :
  ∀ {Index} (fixedPoint : SelectedConstraintNormalFixedPoint Index)
    epsilon timeMagnitude directionScale →
  0ℚ ≤ L1.vectorL1 (coordinates fixedPoint) (uncorrectedResidual fixedPoint) →
  L1.vectorL1 (coordinates fixedPoint) (uncorrectedResidual fixedPoint)
    ≤ epsilon * timeMagnitude * directionScale →
  L1.vectorL1 (coordinates fixedPoint) (correction fixedPoint)
    ≤ (Quarter.fourThirds * epsilon) * timeMagnitude * directionScale
selectedConstraintKernelLineCorrectionLittleO
    fixedPoint epsilon timeMagnitude directionScale residualNN residualUpper =
  let
    fixedPointUpper = selectedConstraintFixedPointResidualBound fixedPoint
    scaledResidual =
      Norm.scaleNonnegative Quarter.fourThirds
        (ℚP.nonNegative⁻¹ Quarter.fourThirds)
        residualUpper
  in
  ℚP.≤-trans fixedPointUpper
    (subst
      (λ upper →
        Quarter.fourThirds
          * L1.vectorL1 (coordinates fixedPoint)
              (uncorrectedResidual fixedPoint)
        ≤ upper)
      (let open import Data.Rational.Tactic.RingSolver as ℚRing
       in ℚRing.solve-∀ epsilon timeMagnitude directionScale)
      scaledResidual)

selectedConstraintZeroResidualForcesZeroCorrection :
  ∀ {Index} (fixedPoint : SelectedConstraintNormalFixedPoint Index) →
  L1.vectorL1 (coordinates fixedPoint) (uncorrectedResidual fixedPoint) ≡ 0ℚ →
  L1.vectorL1 (coordinates fixedPoint) (correction fixedPoint) ≡ 0ℚ
selectedConstraintZeroResidualForcesZeroCorrection fixedPoint residualZero =
  let
    upper = selectedConstraintFixedPointResidualBound fixedPoint
    upperZero :
      L1.vectorL1 (coordinates fixedPoint) (correction fixedPoint) ≤ 0ℚ
    upperZero =
      subst
        (λ upperBound →
          L1.vectorL1 (coordinates fixedPoint) (correction fixedPoint)
          ≤ upperBound)
        (let open import Data.Rational.Tactic.RingSolver as ℚRing
         in ℚRing.solve-∀
           (L1.vectorL1 (coordinates fixedPoint)
             (uncorrectedResidual fixedPoint)))
        (subst
          (λ sourceNorm →
            L1.vectorL1 (coordinates fixedPoint) (correction fixedPoint)
            ≤ Quarter.fourThirds * sourceNorm)
          residualZero upper)
  in
  ℚP.≤-antisym upperZero
    (Reopen.vectorL1Nonnegative
      (coordinates fixedPoint) (correction fixedPoint))

cmp109SelectedConstraintFixedPointResidualLevel : ProofLevel
cmp109SelectedConstraintFixedPointResidualLevel = machineChecked

cmp109SelectedConstraintKernelLineLittleOTransferLevel : ProofLevel
cmp109SelectedConstraintKernelLineLittleOTransferLevel = machineChecked
