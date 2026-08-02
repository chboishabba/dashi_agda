module DASHI.Physics.YangMills.BalabanClayGate4PhysicalClosureRound5IntegratedExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (length)
open import Data.Rational using (1ℚ; _+_; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Foundations.BishopConstructiveRealBridgeExact as Bishop
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PhysicalScaleGeometryExact as Physical
import DASHI.Physics.YangMills.BalabanClayGate4CMP109MinimalAdmissibleRepositoryScaleExact as Minimal
import DASHI.Physics.YangMills.BalabanClayGate4CMP109MinimalEquation012Exact as MinimalEquation012
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PrintedPathFormulaExact as Printed
import DASHI.Physics.YangMills.BalabanClayGate4BishopSU2HalfRadiusInstantiationExact as BishopSU2
import DASHI.Physics.YangMills.BalabanClayGate4SU2HalfRadiusScalarEnvelopeExact as HalfRadius
import DASHI.Physics.YangMills.BalabanClayGate4NewtonFourChannelQuarterExact as Newton
import DASHI.Physics.YangMills.BalabanClayGate4QuantitativeContractionBallConstructionExact as Construction
import DASHI.Physics.YangMills.BalabanClayGate4HalfContractionInvariantBallExact as HalfBall
import DASHI.Physics.YangMills.BalabanClayGate4BalabanGaugeFixingProposition5Exact as GaugeSource
import DASHI.Physics.YangMills.BalabanClayGate4GaugeFixingProposition5ToHalfBallExact as GaugeBridge
import DASHI.Physics.YangMills.BalabanClayGate4QuantitativeImplicitFunctionCommonExact as Quantitative
import DASHI.Physics.YangMills.BalabanClayGate4PhysicalFunctionalSecondVariationExact as Functional
import DASHI.Physics.YangMills.BalabanClayGate4LiteralWilsonLargeFieldPredicateExact as Wilson
import DASHI.Physics.YangMills.BalabanClayGate4WilsonPlaquetteBadCubeBudgetExact as WilsonBudget
import DASHI.Physics.YangMills.BalabanClayGate4DyadicRandomWalkTailExact as RandomWalk
import DASHI.Physics.YangMills.BalabanClayGate4FiveActivityTenthToHalfExact as Activity

------------------------------------------------------------------------
-- Round five owns the strongest concrete instantiations extracted from the
-- previous physical cut.
--
-- * CMP109 uses the minimal source-admissible L=13 repository torus.
-- * Equation (0.12) uses its literal 28561-site block and reciprocal weight.
-- * SU(2) sine and cosine are the actual Bishop power-series values.
-- * Federbush retains the conservative four-channel quarter budget.
-- * Faddeev--Popov/background gauge uses Bałaban Proposition 5's source-exact
--   beta=1/4 domain and contraction factor 1/2.
-- * Wilson, random-walk and activity consequences are exact downstream of
--   local physical estimates.
------------------------------------------------------------------------

record PhysicalClosureRound5Inputs : Set₂ where
  field
    minimalGeometry :
      Physical.CMP109PhysicalScaleGeometry
        Minimal.radius Minimal.RepositoryFineSite
        Minimal.RepositoryCoarseSite Nat

    AveragingField AveragingGroup AveragingLie : Set
    minimalEquation012Inputs :
      MinimalEquation012.MinimalEquation012Inputs
        AveragingField AveragingGroup AveragingLie

    bishopSeriesData : Elementary.BishopElementaryPowerSeriesData
    bishopHalfRadius : BishopSU2.BishopSU2HalfRadiusInputs bishopSeriesData

    FederbushBound : Set
    federbushAlgebra : Newton.FourChannelQuarterAlgebra FederbushBound
    federbushContractionBudget :
      Newton.NewtonFourChannelBudget federbushAlgebra
    federbushForcingBudget :
      Newton.NewtonFourChannelBudget federbushAlgebra

    GaugeConfiguration GaugeCorrection GaugeBound : Set
    gaugeSource : GaugeSource.BalabanGaugeFixingProposition5
      GaugeConfiguration GaugeCorrection GaugeBound
    gaugeTriangle :
      Construction.MetricTriangleBudget GaugeCorrection GaugeBound
    gaugeHalfBudget : HalfBall.HalfContractionBudget gaugeTriangle
    gaugeMetricBridge :
      GaugeBridge.GaugeFixingProposition5MetricBridge
        gaugeSource gaugeTriangle gaugeHalfBudget

    FunctionalCarrier Operator : Set
    secondVariation :
      Functional.AdditiveSecondVariationCalculus FunctionalCarrier Operator
    physicalAtoms :
      Functional.PhysicalFunctionalAtoms
        FunctionalCarrier Operator secondVariation

    WilsonScale Configuration Gauge Block Plaquette : Set
    wilsonLargeField :
      Wilson.LiteralWilsonLargeFieldData
        WilsonScale Configuration Gauge Block Plaquette
    wilsonCost : Wilson.LiteralWilsonCostData wilsonLargeField
    wilsonBadCubeBudget :
      WilsonBudget.WilsonPlaquetteBadCubeBudget wilsonLargeField wilsonCost

    randomWalkOrder : RandomWalk.DyadicRandomWalkOrder
    randomWalkBounds :
      RandomWalk.DyadicRandomWalkShellBound randomWalkOrder

    activityOrder : Activity.RationalAdditiveOrder
    activityAllocation : Activity.FiveActivityTenthAllocation activityOrder

open PhysicalClosureRound5Inputs public

round5MinimalBlockCardinality :
  (inputs : PhysicalClosureRound5Inputs) →
  ∀ coarse →
  length
    (Physical.physicalBlockElements (minimalGeometry inputs) coarse)
  ≡ Minimal.volume
round5MinimalBlockCardinality inputs coarse =
  trans
    (Physical.physicalBlockEnumerationLength
      (minimalGeometry inputs) coarse)
    Minimal.volumeExact

round5MinimalSiteWeightReciprocal :
  Minimal.siteWeightℚ * Minimal.volumeℚ ≡ 1ℚ
round5MinimalSiteWeightReciprocal = Minimal.minimalSiteWeightIsReciprocal

round5MinimalEquation012UsesPhysicalWeight :
  (inputs : PhysicalClosureRound5Inputs) →
  ∀ coarseBond →
  Printed.blockWeight
    (MinimalEquation012.minimalEquation012PrintedData
      (minimalEquation012Inputs inputs)) coarseBond
  ≡ Minimal.siteWeightℚ
round5MinimalEquation012UsesPhysicalWeight inputs =
  MinimalEquation012.minimalEquation012BlockWeight
    (minimalEquation012Inputs inputs)

round5BishopScalarEnvelope :
  (inputs : PhysicalClosureRound5Inputs) →
  HalfRadius.SU2HalfRadiusScalarEnvelope Bishop.Bishopℝ
round5BishopScalarEnvelope inputs =
  BishopSU2.bishopSU2HalfRadiusEnvelope (bishopHalfRadius inputs)

round5FederbushContractionBelowQuarter :
  (inputs : PhysicalClosureRound5Inputs) →
  Newton.LessEqual (federbushAlgebra inputs)
    (Newton.total (federbushContractionBudget inputs))
    (Newton.quarter (federbushAlgebra inputs))
round5FederbushContractionBelowQuarter inputs =
  Newton.newtonFourChannelTotalBelowQuarter
    (federbushContractionBudget inputs)

round5FederbushForcingBelowQuarter :
  (inputs : PhysicalClosureRound5Inputs) →
  Newton.LessEqual (federbushAlgebra inputs)
    (Newton.total (federbushForcingBudget inputs))
    (Newton.quarter (federbushAlgebra inputs))
round5FederbushForcingBelowQuarter inputs =
  Newton.newtonFourChannelTotalBelowQuarter
    (federbushForcingBudget inputs)

round5GaugeInvariantHalfBall :
  (inputs : PhysicalClosureRound5Inputs) →
  Quantitative.InvariantContractionBall
    (Construction.metric (gaugeTriangle inputs))
round5GaugeInvariantHalfBall inputs =
  GaugeBridge.asInvariantGaugeFixingBall (gaugeMetricBridge inputs)

round5GaugeSolutionBound :
  (inputs : PhysicalClosureRound5Inputs) →
  GaugeSource.LessEqual (gaugeSource inputs)
    (GaugeSource.correctionNorm (gaugeSource inputs)
      (GaugeSource.solution (gaugeSource inputs)
        (GaugeBridge.configuration (gaugeMetricBridge inputs))
        (GaugeBridge.admissible (gaugeMetricBridge inputs))))
    (GaugeSource.multiply (gaugeSource inputs)
      (GaugeSource.eight (gaugeSource inputs))
      (GaugeSource.multiply (gaugeSource inputs)
        (GaugeSource.B0Prime (gaugeSource inputs))
        (GaugeSource.multiply (gaugeSource inputs)
          (GaugeSource.B1 (gaugeSource inputs))
          (GaugeSource.add (gaugeSource inputs)
            (GaugeSource.alpha0 (gaugeSource inputs))
            (GaugeSource.alpha1 (gaugeSource inputs))))))
round5GaugeSolutionBound inputs =
  GaugeSource.solutionBound (gaugeSource inputs)
    (GaugeBridge.configuration (gaugeMetricBridge inputs))
    (GaugeBridge.admissible (gaugeMetricBridge inputs))

round5SelectedFunctionalSecondVariation :
  (inputs : PhysicalClosureRound5Inputs) →
  Functional.hessian (secondVariation inputs)
    (Functional.selectedPhysicalFunctional (physicalAtoms inputs))
  ≡ Functional.selectedPhysicalHessian (physicalAtoms inputs)
round5SelectedFunctionalSecondVariation inputs =
  Functional.selectedFunctionalSecondVariationExact (physicalAtoms inputs)

round5WilsonBadPlaquettePaysPenalty :
  (inputs : PhysicalClosureRound5Inputs) →
  ∀ configuration plaquette →
  Wilson.LargePlaquette
    (wilsonLargeField inputs)
    (WilsonBudget.scale (wilsonBadCubeBudget inputs))
    configuration plaquette →
  WilsonBudget.wilsonPenaltyPerBadCube (wilsonBadCubeBudget inputs)
  ≤ Wilson.scaledWilsonPlaquetteCost
      (wilsonCost inputs)
      (WilsonBudget.scale (wilsonBadCubeBudget inputs))
      configuration plaquette
round5WilsonBadPlaquettePaysPenalty inputs =
  WilsonBudget.largePlaquettePaysWilsonBadCubePenalty
    (wilsonBadCubeBudget inputs)

round5RandomWalkPartialBelowDoubleAmplitude :
  (inputs : PhysicalClosureRound5Inputs) →
  ∀ depth →
  RandomWalk.LessEqual (randomWalkOrder inputs)
    (RandomWalk.randomWalkPartialNorm
      (RandomWalk.shellNorm (randomWalkBounds inputs)) depth)
    (RandomWalk.amplitude (randomWalkBounds inputs)
      + RandomWalk.amplitude (randomWalkBounds inputs))
round5RandomWalkPartialBelowDoubleAmplitude inputs =
  RandomWalk.randomWalkPartialBelowDoubleAmplitude
    (randomWalkBounds inputs)

round5FiveActivitiesBelowHalf :
  (inputs : PhysicalClosureRound5Inputs) →
  Activity.LessEqual (activityOrder inputs)
    (Activity.total (activityAllocation inputs))
    (Activity.delta (activityAllocation inputs) * Activity.halfℚ)
round5FiveActivitiesBelowHalf inputs =
  Activity.fiveActivityTotalBelowHalf (activityAllocation inputs)

physicalClosureRound5IntegratedCarrierLevel : ProofLevel
physicalClosureRound5IntegratedCarrierLevel = machineChecked

physicalClosureRound5MinimalCMP109Level : ProofLevel
physicalClosureRound5MinimalCMP109Level = machineChecked

physicalClosureRound5BishopAndFederbushLevel : ProofLevel
physicalClosureRound5BishopAndFederbushLevel = machineChecked

physicalClosureRound5GaugeFixingSourceProfileLevel : ProofLevel
physicalClosureRound5GaugeFixingSourceProfileLevel = machineChecked

physicalClosureRound5FunctionalAndPolymerLevel : ProofLevel
physicalClosureRound5FunctionalAndPolymerLevel = machineChecked
