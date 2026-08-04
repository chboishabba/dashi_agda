module DASHI.Physics.YangMills.BalabanP33FiveChannelPath4CoercivityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- PURPOSE AND DASHI CONTRIBUTION
--
-- Compose the five literal local Hessian mechanisms into the concrete
-- side-four P33 coercivity theorem.  Every channel is a finite signed
-- pointwise family, so its global lower bound is derived rather than supplied.
-- The exact coefficient allocation
--
--   32 + 64 + 32 + 64 + 64 = 256
--
-- and the exact radius 1/8192 then leave the positive floor 1/32.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; -_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; trans)

import DASHI.Physics.YangMills.BalabanClayT3ConfiguredGeometricConstantsExact as Constants
import DASHI.Physics.YangMills.BalabanP33FiniteSignedRemainderSummationExact as Signed
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33
import DASHI.Physics.YangMills.BalabanPath4BondHodgeCoercivityExact as Hodge
open import DASHI.Physics.YangMills.CompactLieProofLevel

record FiveChannelPath4Data
    (Background CurvatureCell TransportCell ChartCell GaugeCell
      ConstraintCell : Set) : Set₁ where
  field
    curvature : Signed.FiniteSignedRemainderFamily
      Background Hodge.RationalBondField4 CurvatureCell
    transport : Signed.FiniteSignedRemainderFamily
      Background Hodge.RationalBondField4 TransportCell
    chart : Signed.FiniteSignedRemainderFamily
      Background Hodge.RationalBondField4 ChartCell
    gauge : Signed.FiniteSignedRemainderFamily
      Background Hodge.RationalBondField4 GaugeCell
    constraint : Signed.FiniteSignedRemainderFamily
      Background Hodge.RationalBondField4 ConstraintCell

    radius : Background → Hodge.RationalBondField4 → ℚ

    curvatureWeightExact : ∀ background state →
      Signed.weight curvature background state
      ≡ Constants.configuredCurvatureCoefficient * radius background state
    transportWeightExact : ∀ background state →
      Signed.weight transport background state
      ≡ Constants.configuredTransportCoefficient * radius background state
    chartWeightExact : ∀ background state →
      Signed.weight chart background state
      ≡ Constants.configuredChartCoefficient * radius background state
    gaugeWeightExact : ∀ background state →
      Signed.weight gauge background state
      ≡ Constants.configuredGaugeCoefficient * radius background state
    constraintWeightExact : ∀ background state →
      Signed.weight constraint background state
      ≡ Constants.configuredConstraintCoefficient * radius background state

    curvatureNormExact : ∀ background state →
      Signed.globalNormSq curvature background state
      ≡ Hodge.bondNormSq state
    transportNormExact : ∀ background state →
      Signed.globalNormSq transport background state
      ≡ Hodge.bondNormSq state
    chartNormExact : ∀ background state →
      Signed.globalNormSq chart background state
      ≡ Hodge.bondNormSq state
    gaugeNormExact : ∀ background state →
      Signed.globalNormSq gauge background state
      ≡ Hodge.bondNormSq state
    constraintNormExact : ∀ background state →
      Signed.globalNormSq constraint background state
      ≡ Hodge.bondNormSq state

    radiusIsConfigured : ∀ background state →
      radius background state ≡ P33.p33SmallFieldRadius

open FiveChannelPath4Data public

curvatureBudgetExact :
  ∀ {Background CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell}
    (dataSet : FiveChannelPath4Data
      Background CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell)
    background state →
  Signed.weight (curvature dataSet) background state
    * Signed.globalNormSq (curvature dataSet) background state
  ≡ Constants.configuredCurvatureCoefficient
    * radius dataSet background state * Hodge.bondNormSq state
curvatureBudgetExact dataSet background state =
  cong₂ _*_
    (curvatureWeightExact dataSet background state)
    (curvatureNormExact dataSet background state)

transportBudgetExact :
  ∀ {Background CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell}
    (dataSet : FiveChannelPath4Data
      Background CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell)
    background state →
  Signed.weight (transport dataSet) background state
    * Signed.globalNormSq (transport dataSet) background state
  ≡ Constants.configuredTransportCoefficient
    * radius dataSet background state * Hodge.bondNormSq state
transportBudgetExact dataSet background state =
  cong₂ _*_
    (transportWeightExact dataSet background state)
    (transportNormExact dataSet background state)

chartBudgetExact :
  ∀ {Background CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell}
    (dataSet : FiveChannelPath4Data
      Background CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell)
    background state →
  Signed.weight (chart dataSet) background state
    * Signed.globalNormSq (chart dataSet) background state
  ≡ Constants.configuredChartCoefficient
    * radius dataSet background state * Hodge.bondNormSq state
chartBudgetExact dataSet background state =
  cong₂ _*_
    (chartWeightExact dataSet background state)
    (chartNormExact dataSet background state)

gaugeBudgetExact :
  ∀ {Background CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell}
    (dataSet : FiveChannelPath4Data
      Background CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell)
    background state →
  Signed.weight (gauge dataSet) background state
    * Signed.globalNormSq (gauge dataSet) background state
  ≡ Constants.configuredGaugeCoefficient
    * radius dataSet background state * Hodge.bondNormSq state
gaugeBudgetExact dataSet background state =
  cong₂ _*_
    (gaugeWeightExact dataSet background state)
    (gaugeNormExact dataSet background state)

constraintBudgetExact :
  ∀ {Background CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell}
    (dataSet : FiveChannelPath4Data
      Background CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell)
    background state →
  Signed.weight (constraint dataSet) background state
    * Signed.globalNormSq (constraint dataSet) background state
  ≡ Constants.configuredConstraintCoefficient
    * radius dataSet background state * Hodge.bondNormSq state
constraintBudgetExact dataSet background state =
  cong₂ _*_
    (constraintWeightExact dataSet background state)
    (constraintNormExact dataSet background state)

channelLowerAtConfiguredBudget :
  ∀ {Background State Cell}
    (family : Signed.FiniteSignedRemainderFamily Background State Cell)
    (coefficient radius normSq : Background → State → ℚ) →
  (∀ background state →
    Signed.weight family background state
      * Signed.globalNormSq family background state
    ≡ coefficient background state * radius background state * normSq background state) →
  ∀ background state →
  - (coefficient background state * radius background state * normSq background state)
  ≤ Signed.globalRemainder family background state
channelLowerAtConfiguredBudget family coefficient radius normSq budgetExact
    background state =
  subst
    (λ lower → lower ≤ Signed.globalRemainder family background state)
    (cong -_ (budgetExact background state))
    (Signed.globalRemainderLowerBound family background state)

totalSignedRemainder :
  ∀ {Background CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell} →
  FiveChannelPath4Data
    Background CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell →
  Background → Hodge.RationalBondField4 → ℚ
totalSignedRemainder dataSet background state =
  Signed.globalRemainder (curvature dataSet) background state
  + (Signed.globalRemainder (transport dataSet) background state
  + (Signed.globalRemainder (chart dataSet) background state
  + (Signed.globalRemainder (gauge dataSet) background state
  + Signed.globalRemainder (constraint dataSet) background state)))

configuredFiveNegativeBudgetsExact : ∀ radiusValue normSqValue →
  - (Constants.configuredCurvatureCoefficient * radiusValue * normSqValue)
  + (- (Constants.configuredTransportCoefficient * radiusValue * normSqValue)
  + (- (Constants.configuredChartCoefficient * radiusValue * normSqValue)
  + (- (Constants.configuredGaugeCoefficient * radiusValue * normSqValue)
  + - (Constants.configuredConstraintCoefficient * radiusValue * normSqValue))))
  ≡ - (Constants.configuredTotalCoefficient * radiusValue * normSqValue)
configuredFiveNegativeBudgetsExact = ℚRing.solve-∀

fiveChannelSignedRemainderLowerBound :
  ∀ {Background CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell}
    (dataSet : FiveChannelPath4Data
      Background CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell)
    background state →
  - (Constants.configuredTotalCoefficient
      * radius dataSet background state
      * Hodge.bondNormSq state)
  ≤ totalSignedRemainder dataSet background state
fiveChannelSignedRemainderLowerBound dataSet background state =
  subst
    (λ lower → lower ≤ totalSignedRemainder dataSet background state)
    (configuredFiveNegativeBudgetsExact
      (radius dataSet background state)
      (Hodge.bondNormSq state))
    (ℚP.+-mono-≤
      curvatureLower
      (ℚP.+-mono-≤
        transportLower
        (ℚP.+-mono-≤
          chartLower
          (ℚP.+-mono-≤ gaugeLower constraintLower))))
  where
  curvatureLower = channelLowerAtConfiguredBudget
    (curvature dataSet)
    (λ _ _ → Constants.configuredCurvatureCoefficient)
    (radius dataSet)
    (λ _ stateValue → Hodge.bondNormSq stateValue)
    (curvatureBudgetExact dataSet)
    background state

  transportLower = channelLowerAtConfiguredBudget
    (transport dataSet)
    (λ _ _ → Constants.configuredTransportCoefficient)
    (radius dataSet)
    (λ _ stateValue → Hodge.bondNormSq stateValue)
    (transportBudgetExact dataSet)
    background state

  chartLower = channelLowerAtConfiguredBudget
    (chart dataSet)
    (λ _ _ → Constants.configuredChartCoefficient)
    (radius dataSet)
    (λ _ stateValue → Hodge.bondNormSq stateValue)
    (chartBudgetExact dataSet)
    background state

  gaugeLower = channelLowerAtConfiguredBudget
    (gauge dataSet)
    (λ _ _ → Constants.configuredGaugeCoefficient)
    (radius dataSet)
    (λ _ stateValue → Hodge.bondNormSq stateValue)
    (gaugeBudgetExact dataSet)
    background state

  constraintLower = channelLowerAtConfiguredBudget
    (constraint dataSet)
    (λ _ _ → Constants.configuredConstraintCoefficient)
    (radius dataSet)
    (λ _ stateValue → Hodge.bondNormSq stateValue)
    (constraintBudgetExact dataSet)
    background state

fiveChannelConfiguredRadiusLowerBound :
  ∀ {Background CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell}
    (dataSet : FiveChannelPath4Data
      Background CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell)
    background state →
  - (Constants.configuredTotalCoefficient
      * P33.p33SmallFieldRadius
      * Hodge.bondNormSq state)
  ≤ totalSignedRemainder dataSet background state
fiveChannelConfiguredRadiusLowerBound dataSet background state =
  subst
    (λ lower → lower ≤ totalSignedRemainder dataSet background state)
    (cong -_
      (cong
        (λ radiusValue →
          Constants.configuredTotalCoefficient
          * radiusValue * Hodge.bondNormSq state)
        (radiusIsConfigured dataSet background state)))
    (fiveChannelSignedRemainderLowerBound dataSet background state)

fiveLocalChannelsGivePath4PhysicalCoercivity :
  ∀ {Background CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell}
    (dataSet : FiveChannelPath4Data
      Background CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell)
    background state gaugeFixingEnergy blockPenaltyEnergy →
  Hodge.BondComponentMeanZero state →
  0ℚ ≤ gaugeFixingEnergy →
  0ℚ ≤ blockPenaltyEnergy →
  P33.p33PhysicalFloor * Hodge.bondNormSq state
  ≤ P33.physicalHessianEnergy
      (Hodge.referenceHodgeEnergy
        state gaugeFixingEnergy blockPenaltyEnergy)
      (totalSignedRemainder dataSet background state)
fiveLocalChannelsGivePath4PhysicalCoercivity
    dataSet background state gaugeFixingEnergy blockPenaltyEnergy
    meanZero gaugeNonnegative blockNonnegative =
  P33.path4ConfiguredRadiusPhysicalCoercive
    state gaugeFixingEnergy blockPenaltyEnergy
    (totalSignedRemainder dataSet background state)
    meanZero gaugeNonnegative blockNonnegative
    (fiveChannelConfiguredRadiusLowerBound dataSet background state)

p33FiveChannelCoefficientAssemblyLevel : ProofLevel
p33FiveChannelCoefficientAssemblyLevel = machineChecked

p33FiveChannelLocalToGlobalLevel : ProofLevel
p33FiveChannelLocalToGlobalLevel = machineChecked

p33FiveChannelPath4CoercivityLevel : ProofLevel
p33FiveChannelPath4CoercivityLevel = machineChecked
