module DASHI.Physics.YangMills.BalabanP33CMP109DerivativeDifferencePrimitiveExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators",
-- Springer Classics in Mathematics, 1995 reprint.
-- DOI: 10.1007/978-3-642-66282-9.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Specialize the exact four-stage telescope to the nonlinear block-average
-- derivative.  A physical matrix coefficient of
--
--   DQ_A - DQ_0
--
-- is dominated by the norm of the four-stage operator difference, and that
-- norm is bounded by the explicit sum of the four stage-difference products.
-- Therefore the P33 constraint leaf reduces to one scalar comparison
--
--   fourStageDifferenceMajorant <= rho,
--
-- rather than an opaque joint estimate on DQ_A-DQ_0.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4OperatorNormPipelineExact as Pipeline
import DASHI.Physics.YangMills.BalabanP33FourStageOperatorDifferenceExact as Difference

record CMP109DerivativeDifferencePrimitive
    (Operator Cell : Set) : Set₁ where
  field
    algebra : Difference.AdditiveOperatorNormAlgebra Operator ℚ
    pair : Difference.FourStageBackgroundPair Operator ℚ algebra
    normInputs : Difference.FourStageDifferenceNormInputs
      Operator ℚ algebra pair

    radius : ℚ

    orderMeaning :
      Pipeline.LessEqual (Difference.normAlgebra algebra) ≡ _≤_

    majorantBelowRadius :
      Difference.fourStageDifferenceMajorant normInputs ≤ radius

    coordinate : Operator → Cell → ℚ
    coordinateBelowOperatorNorm : ∀ operator cell →
      ∣ coordinate operator cell ∣
      ≤ Pipeline.operatorNorm (Difference.normAlgebra algebra) operator

open CMP109DerivativeDifferencePrimitive public

blockDerivativeDifferenceOperator :
  ∀ {Operator Cell} →
  CMP109DerivativeDifferencePrimitive Operator Cell → Operator
blockDerivativeDifferenceOperator dataSet =
  Difference.subtractOperator (algebra dataSet)
    (Difference.backgroundFourStage (pair dataSet))
    (Difference.referenceFourStage (pair dataSet))

blockDerivativeDifferenceNorm :
  ∀ {Operator Cell} →
  CMP109DerivativeDifferencePrimitive Operator Cell → ℚ
blockDerivativeDifferenceNorm dataSet =
  Pipeline.operatorNorm (Difference.normAlgebra (algebra dataSet))
    (blockDerivativeDifferenceOperator dataSet)

blockDerivativeDifferenceCoordinate :
  ∀ {Operator Cell} →
  CMP109DerivativeDifferencePrimitive Operator Cell → Cell → ℚ
blockDerivativeDifferenceCoordinate dataSet cell =
  coordinate dataSet (blockDerivativeDifferenceOperator dataSet) cell

blockDerivativeDifferenceNormBelowRadius :
  ∀ {Operator Cell}
    (dataSet : CMP109DerivativeDifferencePrimitive Operator Cell) →
  blockDerivativeDifferenceNorm dataSet ≤ radius dataSet
blockDerivativeDifferenceNormBelowRadius dataSet =
  ℚP.≤-trans
    (subst
      (λ relation → relation
        (blockDerivativeDifferenceNorm dataSet)
        (Difference.fourStageDifferenceMajorant (normInputs dataSet)))
      (orderMeaning dataSet)
      (Difference.fourStageDifferenceNormBound
        (algebra dataSet) (pair dataSet) (normInputs dataSet)))
    (majorantBelowRadius dataSet)

blockDerivativeCoordinateBelowNorm :
  ∀ {Operator Cell}
    (dataSet : CMP109DerivativeDifferencePrimitive Operator Cell)
    cell →
  ∣ blockDerivativeDifferenceCoordinate dataSet cell ∣
  ≤ blockDerivativeDifferenceNorm dataSet
blockDerivativeCoordinateBelowNorm dataSet cell =
  coordinateBelowOperatorNorm dataSet
    (blockDerivativeDifferenceOperator dataSet) cell

cmp109DQDifferenceExactTelescopeLevel : ProofLevel
cmp109DQDifferenceExactTelescopeLevel = machineChecked

cmp109DQDifferenceNormReductionLevel : ProofLevel
cmp109DQDifferenceNormReductionLevel = machineChecked

cmp109DQPrimitiveCoordinateLevel : ProofLevel
cmp109DQPrimitiveCoordinateLevel = machineChecked
