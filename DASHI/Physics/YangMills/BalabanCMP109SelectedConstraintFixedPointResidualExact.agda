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
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteMatrixL1ContractionExact as L1
import DASHI.Physics.YangMills.BalabanFiniteStrictContractionReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanCMP109FederbushQuarterReopeningExact as Quarter
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

record SelectedConstraintNormalFixedPoint (Index : Set) : Set₁ where
  field
    coordinates : List Index
    uncorrectedResidual : Reopen.Vector Index
    normalRemainder : Reopen.Vector Index → Reopen.Vector Index
    correction : Reopen.Vector Index

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

selectedConstraintKernelLineCorrectionLittleO :
  ∀ {Index} (fixedPoint : SelectedConstraintNormalFixedPoint Index)
    epsilon timeMagnitude directionScale →
  L1.vectorL1 (coordinates fixedPoint) (uncorrectedResidual fixedPoint)
    ≤ epsilon * timeMagnitude * directionScale →
  L1.vectorL1 (coordinates fixedPoint) (correction fixedPoint)
    ≤ (Quarter.fourThirds * epsilon) * timeMagnitude * directionScale
selectedConstraintKernelLineCorrectionLittleO
    fixedPoint epsilon timeMagnitude directionScale residualUpper =
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
      (ℚRing.solve-∀ epsilon timeMagnitude directionScale)
      scaledResidual)

selectedConstraintZeroResidualForcesZeroCorrection :
  ∀ {Index} (fixedPoint : SelectedConstraintNormalFixedPoint Index) →
  L1.vectorL1 (coordinates fixedPoint) (uncorrectedResidual fixedPoint) ≡ 0ℚ →
  L1.vectorL1 (coordinates fixedPoint) (correction fixedPoint) ≡ 0ℚ
selectedConstraintZeroResidualForcesZeroCorrection fixedPoint residualZero =
  let
    upper = selectedConstraintFixedPointResidualBound fixedPoint
    upperWithZeroSource :
      L1.vectorL1 (coordinates fixedPoint) (correction fixedPoint)
      ≤ Quarter.fourThirds * 0ℚ
    upperWithZeroSource =
      subst
        (λ sourceNorm →
          L1.vectorL1 (coordinates fixedPoint) (correction fixedPoint)
          ≤ Quarter.fourThirds * sourceNorm)
        residualZero upper

    upperZero :
      L1.vectorL1 (coordinates fixedPoint) (correction fixedPoint) ≤ 0ℚ
    upperZero =
      subst
        (λ upperBound →
          L1.vectorL1 (coordinates fixedPoint) (correction fixedPoint)
          ≤ upperBound)
        (ℚRing.solve [] : Quarter.fourThirds * 0ℚ ≡ 0ℚ)
        upperWithZeroSource
  in
  ℚP.≤-antisym upperZero
    (Reopen.vectorL1Nonnegative
      (coordinates fixedPoint) (correction fixedPoint))

cmp109SelectedConstraintFixedPointResidualLevel : ProofLevel
cmp109SelectedConstraintFixedPointResidualLevel = machineChecked

cmp109SelectedConstraintKernelLineLittleOTransferLevel : ProofLevel
cmp109SelectedConstraintKernelLineLittleOTransferLevel = machineChecked
