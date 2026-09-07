module DASHI.Foundations.Base369NDimParetoChartExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.SSPTritCarrier as Trit
import DASHI.Foundations.Base369Ternary27DiscriminatorPortfolioBridgeExact as Portfolio
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Core.NDimParetoHyperfabricExact as NDim

------------------------------------------------------------------------
-- BASE369 AS AN EXPLICIT NINE-AXIS PARETO VISUALISATION CHART
--
-- The scheduler semantics are nine distinct axes grouped 3+3+3.  The Base369
-- carrier is therefore a chart of ternary axis levels, not the Pareto order
-- itself.  Pareto dominance remains defined on the application cost functions.
------------------------------------------------------------------------

data SchedulerAxis9 : Set where
  gainAxis relevanceAxis splitAxis
  costAxis authorityAxis permissionAxis
  targetAxis pathAxis closureAxis
  : SchedulerAxis9

schedulerAxisCount : Nat
schedulerAxisCount = 9

schedulerAxisCountIsNine : schedulerAxisCount ≡ 9
schedulerAxisCountIsNine = refl

data AxisView : Set where
  epistemicView governanceView adaptiveContextView : AxisView

axisView : SchedulerAxis9 → AxisView
axisView gainAxis = epistemicView
axisView relevanceAxis = epistemicView
axisView splitAxis = epistemicView
axisView costAxis = governanceView
axisView authorityAxis = governanceView
axisView permissionAxis = governanceView
axisView targetAxis = adaptiveContextView
axisView pathAxis = adaptiveContextView
axisView closureAxis = adaptiveContextView

portfolioAxisTrit :
  Portfolio.DiscriminatorPortfolioFabric → SchedulerAxis9 → Trit.SSPTrit
portfolioAxisTrit p gainAxis =
  Portfolio.gainTrit (Portfolio.gain (Portfolio.epistemic p))
portfolioAxisTrit p relevanceAxis =
  Portfolio.relevanceTrit (Portfolio.relevance (Portfolio.epistemic p))
portfolioAxisTrit p splitAxis =
  Portfolio.splitTrit (Portfolio.splitting (Portfolio.epistemic p))
portfolioAxisTrit p costAxis =
  Portfolio.costTrit (Portfolio.costDesirability (Portfolio.governance p))
portfolioAxisTrit p authorityAxis =
  Portfolio.authorityTrit (Portfolio.authority (Portfolio.governance p))
portfolioAxisTrit p permissionAxis =
  Portfolio.permissionTrit (Portfolio.permission (Portfolio.governance p))
portfolioAxisTrit p targetAxis =
  Portfolio.resolutionTrit (Portfolio.targetResolution (Portfolio.context p))
portfolioAxisTrit p pathAxis =
  Portfolio.resolutionTrit (Portfolio.pathResolution (Portfolio.context p))
portfolioAxisTrit p closureAxis =
  Portfolio.resolutionTrit (Portfolio.consumerClosure (Portfolio.context p))

canonicalGainIsPositive :
  portfolioAxisTrit Portfolio.canonicalCandidate gainAxis ≡ Trit.sspPosOne
canonicalGainIsPositive = refl

canonicalPathIsNeutral :
  portfolioAxisTrit Portfolio.canonicalCandidate pathAxis ≡ Trit.sspZero
canonicalPathIsNeutral = refl

canonicalClosureIsNegative :
  portfolioAxisTrit Portfolio.canonicalCandidate closureAxis ≡ Trit.sspNegOne
canonicalClosureIsNegative = refl

ternaryNineAxisProfileCount : Nat
ternaryNineAxisProfileCount = 19683

ternaryNineAxisProfileCountMatchesBase369 :
  ternaryNineAxisProfileCount ≡ Geometry.hyperfabricStateCount
ternaryNineAxisProfileCountMatchesBase369 = refl

record Base369NDimParetoChartBoundary : Set where
  constructor base369NDimParetoChartBoundary
  field
    chartHasNineDeclaredSemanticAxes : Bool
    axesAreGroupedThreePlusThreePlusThree : Bool
    eachThreeAxisGroupHasTwentySevenTernaryProfiles : Bool
    fullNineAxisTernaryChartHas19683Profiles : Bool
    profileCountEqualsParetoDimension : Bool
    ternaryCoordinateOrderAutomaticallyEqualsApplicationCostOrder : Bool
    groupingAxesIntoVoxelsChangesParetoSemantics : Bool

canonicalBase369NDimParetoChartBoundary : Base369NDimParetoChartBoundary
canonicalBase369NDimParetoChartBoundary =
  base369NDimParetoChartBoundary true true true true false false false

existingNDimBoundary : NDim.NDimParetoHyperfabricBoundary
existingNDimBoundary = NDim.canonicalNDimParetoHyperfabricBoundary
