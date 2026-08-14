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
-- The correct physical Hodge remainder is
--
--   [H_W-H_curl] + [H_gf-H_div],
--
-- measured with the literal three-component SU(2) norm.  Its combined budget
-- is
--
--   epsilon_W + epsilon_gf = 1549/196608,
--
-- leaving
--
--   1/32 - (epsilon_W+epsilon_gf) = 4595/196608 > 0.
--
-- This module proves the exact rational aggregation and the final physical
-- coercivity promotion.  The still-open analytic producers are accurately
-- separated: a physical sixteen-atom Wilson estimate and a physical gauge
-- perturbation estimate.  No Wilson-only or one-component shortcut remains.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; -_; _≤_; _/_; NonNegative)
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
import DASHI.Physics.YangMills.BalabanClayT3ConfiguredGeometricConstantsExact as Constants
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33
import DASHI.Physics.YangMills.BalabanPath4BondHodgeCoercivityExact as ScalarHodge
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2HodgeCoercivityExact as PhysicalHodge
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
-- Nonnegativity of the literal scalar and physical norms.
------------------------------------------------------------------------

scalarGlobalNormSqNonnegative :
  ∀ fieldValue → 0ℚ ≤ Variance.globalNormSq fieldValue
scalarGlobalNormSqNonnegative fieldValue =
  Schur.sumNonnegative
    (Block.physicalBlockSites Path4.side4)
    (λ site → fieldValue site * fieldValue site)
    (λ site → FiniteL2.squareNonnegative (fieldValue site))

scalarBondNormSqNonnegative :
  ∀ fieldValue → 0ℚ ≤ ScalarHodge.bondNormSq fieldValue
scalarBondNormSqNonnegative fieldValue =
  Schur.sumNonnegative
    (Torus.allCyclicIndices Torus.four)
    (λ axis → Variance.globalNormSq (ScalarHodge.bondComponent fieldValue axis))
    (λ axis →
      scalarGlobalNormSqNonnegative
        (ScalarHodge.bondComponent fieldValue axis))

physicalBondNormSqNonnegative :
  ∀ fieldValue → 0ℚ ≤ Physical.physicalSU2BondNormSq fieldValue
physicalBondNormSqNonnegative fieldValue =
  ℚP.+-mono-≤
    (ℚP.+-mono-≤
      (scalarBondNormSqNonnegative (fieldValue Physical.coordinateX))
      (scalarBondNormSqNonnegative (fieldValue Physical.coordinateY)))
    (scalarBondNormSqNonnegative (fieldValue Physical.coordinateZ))

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
-- Separate physical Wilson and gauge estimates imply 1/32 coercivity.
------------------------------------------------------------------------

literalHessianCoerciveFromSharpWilsonGaugeBudgets :
  ∀ {Plaquette GaugeIndex ConstraintIndex}
    (fieldValue : Physical.PhysicalSU2BondField4)
    (dataSet : Jets.LiteralPhysicalSecondVariation
      Plaquette GaugeIndex ConstraintIndex)
    flatCurlEnergy flatDivergenceEnergy →
  PhysicalHodge.PhysicalBondComponentMeanZero fieldValue →
  Jets.ExactResidualBackground (Jets.gaugeResidual dataSet) →
  Jets.ExactResidualBackground (Jets.constraintResidual dataSet) →
  PhysicalHodge.physicalReferenceDifferenceEnergy fieldValue
    ≡ flatCurlEnergy + flatDivergenceEnergy →
  - (Sharp.sharpSixteenAtomBudget * Physical.physicalSU2BondNormSq fieldValue)
    ≤ Jets.wilsonSecondVariation dataSet - flatCurlEnergy →
  - (configuredGaugeHodgeBudget * Physical.physicalSU2BondNormSq fieldValue)
    ≤ Cancel.gaugeFirstEnergy dataSet - flatDivergenceEnergy →
  P33.p33PhysicalFloor * Physical.physicalSU2BondNormSq fieldValue
    ≤ Jets.literalTotalSecondVariation dataSet
literalHessianCoerciveFromSharpWilsonGaugeBudgets
    fieldValue dataSet flatCurlEnergy flatDivergenceEnergy
    meanZero gaugeExact constraintExact referenceExact
    wilsonLower gaugeLower =
  let
    splitLower :
      - (sharpWilsonGaugeBudget * Physical.physicalSU2BondNormSq fieldValue)
      ≤ (Jets.wilsonSecondVariation dataSet - flatCurlEnergy)
        + (Cancel.gaugeFirstEnergy dataSet - flatDivergenceEnergy)
    splitLower =
      coupledSignedLowerFromSeparateBudgets
        (Physical.physicalSU2BondNormSq fieldValue)
        (Jets.wilsonSecondVariation dataSet - flatCurlEnergy)
        (Cancel.gaugeFirstEnergy dataSet - flatDivergenceEnergy)
        wilsonLower gaugeLower

    coupledLower :
      - (sharpWilsonGaugeBudget * Physical.physicalSU2BondNormSq fieldValue)
      ≤ Jets.wilsonSecondVariation dataSet
          + Cancel.gaugeFirstEnergy dataSet
          - PhysicalHodge.physicalReferenceDifferenceEnergy fieldValue
    coupledLower =
      subst
        (λ upper →
          - (sharpWilsonGaugeBudget * Physical.physicalSU2BondNormSq fieldValue)
          ≤ upper)
        (sym
          (physicalReferenceTurnsCoupledRemainderIntoLiteralOne
            (Jets.wilsonSecondVariation dataSet)
            (Cancel.gaugeFirstEnergy dataSet)
            (PhysicalHodge.physicalReferenceDifferenceEnergy fieldValue)
            flatCurlEnergy flatDivergenceEnergy referenceExact))
        (subst
          (λ upper →
            - (sharpWilsonGaugeBudget * Physical.physicalSU2BondNormSq fieldValue)
            ≤ upper)
          (sym
            (coupledHodgeRemainderSplits
              (Jets.wilsonSecondVariation dataSet)
              (Cancel.gaugeFirstEnergy dataSet)
              flatCurlEnergy flatDivergenceEnergy))
          splitLower)

    physicalLower :
      - (P33.p33PhysicalFloor * Physical.physicalSU2BondNormSq fieldValue)
      ≤ Jets.wilsonSecondVariation dataSet
          + Cancel.gaugeFirstEnergy dataSet
          - PhysicalHodge.physicalReferenceDifferenceEnergy fieldValue
    physicalLower =
      sharpCoupledLowerImpliesPhysicalSignedLower
        (Physical.physicalSU2BondNormSq fieldValue)
        (Jets.wilsonSecondVariation dataSet
          + Cancel.gaugeFirstEnergy dataSet
          - PhysicalHodge.physicalReferenceDifferenceEnergy fieldValue)
        (physicalBondNormSqNonnegative fieldValue)
        coupledLower
  in
  Cancel.literalHessianCoerciveFromWilsonGaugeHodgeDifference
    fieldValue dataSet meanZero gaugeExact constraintExact physicalLower

sharpWilsonGaugeBudgetGapLevel : ProofLevel
sharpWilsonGaugeBudgetGapLevel = machineChecked

coupledWilsonGaugeSignedPromotionLevel : ProofLevel
coupledWilsonGaugeSignedPromotionLevel = machineChecked

literalPhysicalNormNonnegativeLevel : ProofLevel
literalPhysicalNormNonnegativeLevel = machineChecked

flatHodgeRemainderDecompositionLevel : ProofLevel
flatHodgeRemainderDecompositionLevel = machineChecked

literalSharpWilsonGaugeCoercivityLevel : ProofLevel
literalSharpWilsonGaugeCoercivityLevel = machineChecked

physicalSharpWilsonAtomEstimateLevel : ProofLevel
physicalSharpWilsonAtomEstimateLevel = conditional

physicalGaugeHodgeEstimateLevel : ProofLevel
physicalGaugeHodgeEstimateLevel = conditional
