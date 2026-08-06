module DASHI.Physics.YangMills.BalabanP33WilsonSharpBudgetCoercivityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Connect the sharp sixteen-atom Wilson budget to the exact gauge/constraint
-- cancellation theorem.  At rho=1/8192 the available sharp Wilson coefficient
-- is
--
--   epsilon_W = (13/24) rho = 13/196608.
--
-- The physical coercivity budget is
--
--   1/32 = 6144/196608,
--
-- leaving the exact positive gap
--
--   1/32 - epsilon_W = 6131/196608.
--
-- Hence the signed Wilson estimate
--
--   -epsilon_W ||h||^2 <= H_W''[h,h]-H_diff[h,h]
--
-- is much stronger than the lower bound required for 1/32 literal Hessian
-- coercivity after the exact gauge and constraint squares cancel.  This module
-- proves the complete ordered-rational promotion, including nonnegativity of
-- the literal bond norm.  The physical identification and estimate of the
-- sixteen Wilson atoms remains the sole analytic producer.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using
  (ℚ; 0ℚ; _+_; _*_; -_; _≤_; _/_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanPath4PhysicalVarianceDecompositionExact as Variance
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanP33WilsonSharpDuhamelBudgetExact as Sharp
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33
import DASHI.Physics.YangMills.BalabanPath4BondHodgeCoercivityExact as Hodge
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintSecondVariationExact as Jets
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintCancellationExact as Cancel

------------------------------------------------------------------------
-- Exact scalar budget comparison.
------------------------------------------------------------------------

sharpWilsonGap : ℚ
sharpWilsonGap = + 6131 / 196608

sharpWilsonGapNonnegative : 0ℚ ≤ sharpWilsonGap
sharpWilsonGapNonnegative = ℚP.nonNegative⁻¹ sharpWilsonGap

sharpBudgetPlusGapIsPhysicalFloor :
  Sharp.sharpSixteenAtomBudget + sharpWilsonGap
  ≡ P33.p33PhysicalFloor
sharpBudgetPlusGapIsPhysicalFloor = ℚRing.solve []

sharpWilsonBudgetBelowPhysicalFloor :
  Sharp.sharpSixteenAtomBudget ≤ P33.p33PhysicalFloor
sharpWilsonBudgetBelowPhysicalFloor =
  let
    instance
      gapNN : NonNegative sharpWilsonGap
      gapNN = ℚ.nonNegative sharpWilsonGapNonnegative

    beforeRewrite :
      Sharp.sharpSixteenAtomBudget
      ≤ Sharp.sharpSixteenAtomBudget + sharpWilsonGap
    beforeRewrite =
      ℚP.p≤p+q Sharp.sharpSixteenAtomBudget sharpWilsonGap
  in
  subst
    (λ upper → Sharp.sharpSixteenAtomBudget ≤ upper)
    sharpBudgetPlusGapIsPhysicalFloor
    beforeRewrite

negateOrderReverse : ∀ left right →
  left ≤ right → - right ≤ - left
negateOrderReverse left right leftBelowRight =
  let
    shifted :
      left + - (left + right)
      ≤ right + - (left + right)
    shifted =
      ℚP.+-mono-≤ leftBelowRight ℚP.≤-refl
  in
  subst
    (λ lower → lower ≤ - left)
    (ℚRing.solve-∀ left right)
    (subst
      (λ upper → left + - (left + right) ≤ upper)
      (ℚRing.solve-∀ left right)
      shifted)

sharpSignedLowerImpliesPhysicalSignedLower :
  ∀ normSq remainder →
  0ℚ ≤ normSq →
  - (Sharp.sharpSixteenAtomBudget * normSq) ≤ remainder →
  - (P33.p33PhysicalFloor * normSq) ≤ remainder
sharpSignedLowerImpliesPhysicalSignedLower
    normSq remainder normNonnegative sharpLower =
  let
    instance
      normNN : NonNegative normSq
      normNN = ℚ.nonNegative normNonnegative

    scaledBudget :
      Sharp.sharpSixteenAtomBudget * normSq
      ≤ P33.p33PhysicalFloor * normSq
    scaledBudget =
      ℚP.*-monoʳ-≤-nonNeg
        normSq sharpWilsonBudgetBelowPhysicalFloor

    reversed :
      - (P33.p33PhysicalFloor * normSq)
      ≤ - (Sharp.sharpSixteenAtomBudget * normSq)
    reversed =
      negateOrderReverse
        (Sharp.sharpSixteenAtomBudget * normSq)
        (P33.p33PhysicalFloor * normSq)
        scaledBudget
  in
  ℚP.≤-trans reversed sharpLower

------------------------------------------------------------------------
-- The literal bond norm is a finite sum of finite sums of squares.
------------------------------------------------------------------------

globalNormSqNonnegative :
  ∀ field → 0ℚ ≤ Variance.globalNormSq field
globalNormSqNonnegative field =
  Schur.sumNonnegative
    (Block.physicalBlockSites Path4.side4)
    (λ site → field site * field site)
    (λ site → FiniteL2.squareNonnegative (field site))

bondNormSqNonnegative :
  ∀ field → 0ℚ ≤ Hodge.bondNormSq field
bondNormSqNonnegative field =
  Schur.sumNonnegative
    (Torus.allCyclicIndices Torus.four)
    (λ axis → Variance.globalNormSq (Hodge.bondComponent field axis))
    (λ axis →
      globalNormSqNonnegative (Hodge.bondComponent field axis))

------------------------------------------------------------------------
-- Sharp Wilson estimate implies the literal 1/32 Hessian theorem.
------------------------------------------------------------------------

literalHessianCoerciveFromSharpWilsonBudget :
  ∀ {Plaquette GaugeIndex ConstraintIndex}
    (field : Hodge.RationalBondField4)
    (data : Jets.LiteralPhysicalSecondVariation
      Plaquette GaugeIndex ConstraintIndex) →
  Hodge.BondComponentMeanZero field →
  Jets.ExactResidualBackground (Jets.gaugeResidual data) →
  Jets.ExactResidualBackground (Jets.constraintResidual data) →
  - (Sharp.sharpSixteenAtomBudget * Hodge.bondNormSq field)
    ≤ Jets.wilsonSecondVariation data
        - Hodge.bondReferenceDifferenceEnergy field →
  P33.p33PhysicalFloor * Hodge.bondNormSq field
    ≤ Jets.literalTotalSecondVariation data
literalHessianCoerciveFromSharpWilsonBudget
    field data meanZero gaugeExact constraintExact sharpLower =
  Cancel.literalHessianCoerciveFromWilsonDifference
    field data meanZero gaugeExact constraintExact
    (sharpSignedLowerImpliesPhysicalSignedLower
      (Hodge.bondNormSq field)
      (Jets.wilsonSecondVariation data
        - Hodge.bondReferenceDifferenceEnergy field)
      (bondNormSqNonnegative field)
      sharpLower)

sharpWilsonBudgetGapLevel : ProofLevel
sharpWilsonBudgetGapLevel = machineChecked

sharpWilsonSignedPromotionLevel : ProofLevel
sharpWilsonSignedPromotionLevel = machineChecked

literalBondNormNonnegativeLevel : ProofLevel
literalBondNormNonnegativeLevel = machineChecked

literalSharpWilsonCoercivityLevel : ProofLevel
literalSharpWilsonCoercivityLevel = machineChecked

physicalSharpWilsonAtomEstimateLevel : ProofLevel
physicalSharpWilsonAtomEstimateLevel = conditional
