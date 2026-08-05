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
-- DASHI CORRECTION AND CONTRIBUTION
--
-- The sharp sixteen-atom Wilson perturbation budget is
--
--   epsilon_W = (13/24) rho = 13/196608,
--
-- while the configured gauge/divergence perturbation budget is
--
--   epsilon_gf = 64 rho = 1536/196608.
--
-- The correct Hodge remainder is coupled:
--
--   [H_W-H_curl] + [H_gf-H_div].
--
-- It is not H_W-H_gradient.  The combined exact budget is
--
--   epsilon_W + epsilon_gf = 1549/196608,
--
-- leaving
--
--   1/32 - (epsilon_W+epsilon_gf) = 4595/196608 > 0.
--
-- This module proves the complete rational aggregation, the decomposition from
-- a flat Hodge identity H_gradient=H_curl+H_div, and the final literal Hessian
-- coercivity promotion.  The remaining analytic producers are now accurately
-- separated: the physical sixteen-atom Wilson estimate and the physical gauge
-- perturbation estimate.  No Wilson-only shortcut is retained.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using
  (ℚ; 0ℚ; _+_; _-_; _*_; -_; _≤_; _/_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanPath4PhysicalVarianceDecompositionExact as Variance
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanP33WilsonSharpDuhamelBudgetExact as Sharp
import DASHI.Physics.YangMills.BalabanClayT3ConfiguredGeometricConstantsExact as Constants
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33
import DASHI.Physics.YangMills.BalabanPath4BondHodgeCoercivityExact as Hodge
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintSecondVariationExact as Jets
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintCancellationExact as Cancel

------------------------------------------------------------------------
-- Exact scalar budgets.
------------------------------------------------------------------------

configuredGaugeHodgeBudget : ℚ
configuredGaugeHodgeBudget =
  Constants.configuredGaugeCoefficient * Sharp.rho

sharpWilsonGaugeBudget : ℚ
sharpWilsonGaugeBudget =
  Sharp.sharpSixteenAtomBudget + configuredGaugeHodgeBudget

sharpWilsonGaugeBudgetExact :
  sharpWilsonGaugeBudget ≡ + 1549 / 196608
sharpWilsonGaugeBudgetExact = ℚRing.solve []

sharpWilsonGaugeGap : ℚ
sharpWilsonGaugeGap = + 4595 / 196608

sharpWilsonGaugeGapNonnegative : 0ℚ ≤ sharpWilsonGaugeGap
sharpWilsonGaugeGapNonnegative =
  ℚP.nonNegative⁻¹ sharpWilsonGaugeGap

sharpWilsonGaugeBudgetPlusGapIsPhysicalFloor :
  sharpWilsonGaugeBudget + sharpWilsonGaugeGap
  ≡ P33.p33PhysicalFloor
sharpWilsonGaugeBudgetPlusGapIsPhysicalFloor = ℚRing.solve []

sharpWilsonGaugeBudgetBelowPhysicalFloor :
  sharpWilsonGaugeBudget ≤ P33.p33PhysicalFloor
sharpWilsonGaugeBudgetBelowPhysicalFloor =
  let
    instance
      gapNN : NonNegative sharpWilsonGaugeGap
      gapNN = ℚ.nonNegative sharpWilsonGaugeGapNonnegative

    beforeRewrite :
      sharpWilsonGaugeBudget
      ≤ sharpWilsonGaugeBudget + sharpWilsonGaugeGap
    beforeRewrite =
      ℚP.p≤p+q sharpWilsonGaugeBudget sharpWilsonGaugeGap
  in
  subst
    (λ upper → sharpWilsonGaugeBudget ≤ upper)
    sharpWilsonGaugeBudgetPlusGapIsPhysicalFloor
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

coupledSignedLowerFromSeparateBudgets :
  ∀ normSq wilsonDefect gaugeDefect →
  - (Sharp.sharpSixteenAtomBudget * normSq) ≤ wilsonDefect →
  - (configuredGaugeHodgeBudget * normSq) ≤ gaugeDefect →
  - (sharpWilsonGaugeBudget * normSq)
    ≤ wilsonDefect + gaugeDefect
coupledSignedLowerFromSeparateBudgets
    normSq wilsonDefect gaugeDefect wilsonLower gaugeLower =
  subst
    (λ lower → lower ≤ wilsonDefect + gaugeDefect)
    (ℚRing.solve-∀
      Sharp.sharpSixteenAtomBudget
      configuredGaugeHodgeBudget normSq)
    (ℚP.+-mono-≤ wilsonLower gaugeLower)

sharpCoupledLowerImpliesPhysicalSignedLower :
  ∀ normSq remainder →
  0ℚ ≤ normSq →
  - (sharpWilsonGaugeBudget * normSq) ≤ remainder →
  - (P33.p33PhysicalFloor * normSq) ≤ remainder
sharpCoupledLowerImpliesPhysicalSignedLower
    normSq remainder normNonnegative sharpLower =
  let
    instance
      normNN : NonNegative normSq
      normNN = ℚ.nonNegative normNonnegative

    scaledBudget :
      sharpWilsonGaugeBudget * normSq
      ≤ P33.p33PhysicalFloor * normSq
    scaledBudget =
      ℚP.*-monoʳ-≤-nonNeg
        normSq sharpWilsonGaugeBudgetBelowPhysicalFloor

    reversed :
      - (P33.p33PhysicalFloor * normSq)
      ≤ - (sharpWilsonGaugeBudget * normSq)
    reversed =
      negateOrderReverse
        (sharpWilsonGaugeBudget * normSq)
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
-- Exact Hodge decomposition of the coupled remainder.
------------------------------------------------------------------------

coupledHodgeRemainder :
  ℚ → ℚ → ℚ → ℚ → ℚ
coupledHodgeRemainder wilson gauge flatCurl flatDivergence =
  (wilson + gauge) - (flatCurl + flatDivergence)

coupledHodgeRemainderSplits :
  ∀ wilson gauge flatCurl flatDivergence →
  coupledHodgeRemainder wilson gauge flatCurl flatDivergence
  ≡ (wilson - flatCurl) + (gauge - flatDivergence)
coupledHodgeRemainderSplits = ℚRing.solve-∀

physicalReferenceTurnsCoupledRemainderIntoLiteralOne :
  ∀ wilson gauge physicalReference flatCurl flatDivergence →
  physicalReference ≡ flatCurl + flatDivergence →
  wilson + gauge - physicalReference
  ≡ coupledHodgeRemainder wilson gauge flatCurl flatDivergence
physicalReferenceTurnsCoupledRemainderIntoLiteralOne
    wilson gauge physicalReference flatCurl flatDivergence referenceExact =
  subst
    (λ selected →
      wilson + gauge - selected
      ≡ coupledHodgeRemainder wilson gauge flatCurl flatDivergence)
    (sym referenceExact)
    (ℚRing.solve [])

------------------------------------------------------------------------
-- Separate Wilson and gauge estimates imply literal 1/32 coercivity.
------------------------------------------------------------------------

literalHessianCoerciveFromSharpWilsonGaugeBudgets :
  ∀ {Plaquette GaugeIndex ConstraintIndex}
    (field : Hodge.RationalBondField4)
    (dataSet : Jets.LiteralPhysicalSecondVariation
      Plaquette GaugeIndex ConstraintIndex)
    flatCurlEnergy flatDivergenceEnergy →
  Hodge.BondComponentMeanZero field →
  Jets.ExactResidualBackground (Jets.gaugeResidual dataSet) →
  Jets.ExactResidualBackground (Jets.constraintResidual dataSet) →
  Hodge.bondReferenceDifferenceEnergy field
    ≡ flatCurlEnergy + flatDivergenceEnergy →
  - (Sharp.sharpSixteenAtomBudget * Hodge.bondNormSq field)
    ≤ Jets.wilsonSecondVariation dataSet - flatCurlEnergy →
  - (configuredGaugeHodgeBudget * Hodge.bondNormSq field)
    ≤ Cancel.gaugeFirstEnergy dataSet - flatDivergenceEnergy →
  P33.p33PhysicalFloor * Hodge.bondNormSq field
    ≤ Jets.literalTotalSecondVariation dataSet
literalHessianCoerciveFromSharpWilsonGaugeBudgets
    field dataSet flatCurlEnergy flatDivergenceEnergy
    meanZero gaugeExact constraintExact referenceExact
    wilsonLower gaugeLower =
  let
    splitLower :
      - (sharpWilsonGaugeBudget * Hodge.bondNormSq field)
      ≤ (Jets.wilsonSecondVariation dataSet - flatCurlEnergy)
        + (Cancel.gaugeFirstEnergy dataSet - flatDivergenceEnergy)
    splitLower =
      coupledSignedLowerFromSeparateBudgets
        (Hodge.bondNormSq field)
        (Jets.wilsonSecondVariation dataSet - flatCurlEnergy)
        (Cancel.gaugeFirstEnergy dataSet - flatDivergenceEnergy)
        wilsonLower gaugeLower

    coupledLower :
      - (sharpWilsonGaugeBudget * Hodge.bondNormSq field)
      ≤ Jets.wilsonSecondVariation dataSet
          + Cancel.gaugeFirstEnergy dataSet
          - Hodge.bondReferenceDifferenceEnergy field
    coupledLower =
      subst
        (λ upper →
          - (sharpWilsonGaugeBudget * Hodge.bondNormSq field) ≤ upper)
        (sym
          (physicalReferenceTurnsCoupledRemainderIntoLiteralOne
            (Jets.wilsonSecondVariation dataSet)
            (Cancel.gaugeFirstEnergy dataSet)
            (Hodge.bondReferenceDifferenceEnergy field)
            flatCurlEnergy flatDivergenceEnergy referenceExact))
        (subst
          (λ upper →
            - (sharpWilsonGaugeBudget * Hodge.bondNormSq field) ≤ upper)
          (sym
            (coupledHodgeRemainderSplits
              (Jets.wilsonSecondVariation dataSet)
              (Cancel.gaugeFirstEnergy dataSet)
              flatCurlEnergy flatDivergenceEnergy))
          splitLower)

    physicalLower :
      - (P33.p33PhysicalFloor * Hodge.bondNormSq field)
      ≤ Jets.wilsonSecondVariation dataSet
          + Cancel.gaugeFirstEnergy dataSet
          - Hodge.bondReferenceDifferenceEnergy field
    physicalLower =
      sharpCoupledLowerImpliesPhysicalSignedLower
        (Hodge.bondNormSq field)
        (Jets.wilsonSecondVariation dataSet
          + Cancel.gaugeFirstEnergy dataSet
          - Hodge.bondReferenceDifferenceEnergy field)
        (bondNormSqNonnegative field)
        coupledLower
  in
  Cancel.literalHessianCoerciveFromWilsonGaugeHodgeDifference
    field dataSet meanZero gaugeExact constraintExact physicalLower

sharpWilsonGaugeBudgetGapLevel : ProofLevel
sharpWilsonGaugeBudgetGapLevel = machineChecked

coupledWilsonGaugeSignedPromotionLevel : ProofLevel
coupledWilsonGaugeSignedPromotionLevel = machineChecked

literalBondNormNonnegativeLevel : ProofLevel
literalBondNormNonnegativeLevel = machineChecked

flatHodgeRemainderDecompositionLevel : ProofLevel
flatHodgeRemainderDecompositionLevel = machineChecked

literalSharpWilsonGaugeCoercivityLevel : ProofLevel
literalSharpWilsonGaugeCoercivityLevel = machineChecked

physicalSharpWilsonAtomEstimateLevel : ProofLevel
physicalSharpWilsonAtomEstimateLevel = conditional

physicalGaugeHodgeEstimateLevel : ProofLevel
physicalGaugeHodgeEstimateLevel = conditional
