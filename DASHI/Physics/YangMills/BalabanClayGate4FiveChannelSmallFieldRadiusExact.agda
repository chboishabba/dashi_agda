module DASHI.Physics.YangMills.BalabanClayGate4FiveChannelSmallFieldRadiusExact where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4FiveChannelSelfAdjointOperatorBoundExact as Five
import DASHI.Physics.YangMills.BalabanClayGate4FiveChannelSixteenthBudgetExact as Sixteenth

------------------------------------------------------------------------
-- Select one small-field radius from five symbolic channel constants.
--
-- The physical estimates naturally have the form epsilon_j <= C_j epsilon.
-- Instead of proving five unrelated one-sixteenth bounds, the consumer supplies
-- the five linear estimates and five scalar target checks C_j epsilon<=1/16.
------------------------------------------------------------------------

record FiveChannelSmallFieldRadius
    {Operator State Bound : Set}
    (dataSet : Five.FiveChannelFormBoundData Operator State Bound)
    (budget : Sixteenth.SixteenthBudgetAlgebra Bound) : Set₁ where
  field
    smallFieldRadius : Bound
    multiply : Bound → Bound → Bound

    curvatureConstant transportConstant chartConstant
      gaugeConstant constraintConstant : Bound

    curvatureLinearEstimate :
      Five.LessEqual dataSet
        (Five.epsilonCurvature dataSet)
        (multiply curvatureConstant smallFieldRadius)
    transportLinearEstimate :
      Five.LessEqual dataSet
        (Five.epsilonTransport dataSet)
        (multiply transportConstant smallFieldRadius)
    chartLinearEstimate :
      Five.LessEqual dataSet
        (Five.epsilonChart dataSet)
        (multiply chartConstant smallFieldRadius)
    gaugeLinearEstimate :
      Five.LessEqual dataSet
        (Five.epsilonGauge dataSet)
        (multiply gaugeConstant smallFieldRadius)
    constraintLinearEstimate :
      Five.LessEqual dataSet
        (Five.epsilonConstraint dataSet)
        (multiply constraintConstant smallFieldRadius)

    curvatureRadiusTarget :
      Five.LessEqual dataSet
        (multiply curvatureConstant smallFieldRadius)
        (Sixteenth.oneSixteenth budget)
    transportRadiusTarget :
      Five.LessEqual dataSet
        (multiply transportConstant smallFieldRadius)
        (Sixteenth.oneSixteenth budget)
    chartRadiusTarget :
      Five.LessEqual dataSet
        (multiply chartConstant smallFieldRadius)
        (Sixteenth.oneSixteenth budget)
    gaugeRadiusTarget :
      Five.LessEqual dataSet
        (multiply gaugeConstant smallFieldRadius)
        (Sixteenth.oneSixteenth budget)
    constraintRadiusTarget :
      Five.LessEqual dataSet
        (multiply constraintConstant smallFieldRadius)
        (Sixteenth.oneSixteenth budget)

    physicalNestedFiveMeaning :
      Five.add dataSet (Sixteenth.oneSixteenth budget)
        (Five.add dataSet (Sixteenth.oneSixteenth budget)
          (Five.add dataSet (Sixteenth.oneSixteenth budget)
            (Five.add dataSet (Sixteenth.oneSixteenth budget)
              (Sixteenth.oneSixteenth budget))))
      ≡ Sixteenth.fiveSixteenths budget

    physicalFiveBelowHalf :
      Five.LessEqual dataSet
        (Sixteenth.fiveSixteenths budget)
        (Sixteenth.half budget)

open FiveChannelSmallFieldRadius public

curvatureBelowSixteenth :
  ∀ {Operator State Bound}
    {dataSet : Five.FiveChannelFormBoundData Operator State Bound}
    {budget : Sixteenth.SixteenthBudgetAlgebra Bound} →
  (radius : FiveChannelSmallFieldRadius dataSet budget) →
  Five.LessEqual dataSet
    (Five.epsilonCurvature dataSet)
    (Sixteenth.oneSixteenth budget)
curvatureBelowSixteenth {dataSet = dataSet} radius =
  Five.transitive dataSet
    (curvatureLinearEstimate radius)
    (curvatureRadiusTarget radius)

transportBelowSixteenth :
  ∀ {Operator State Bound}
    {dataSet : Five.FiveChannelFormBoundData Operator State Bound}
    {budget : Sixteenth.SixteenthBudgetAlgebra Bound} →
  (radius : FiveChannelSmallFieldRadius dataSet budget) →
  Five.LessEqual dataSet
    (Five.epsilonTransport dataSet)
    (Sixteenth.oneSixteenth budget)
transportBelowSixteenth {dataSet = dataSet} radius =
  Five.transitive dataSet
    (transportLinearEstimate radius)
    (transportRadiusTarget radius)

chartBelowSixteenth :
  ∀ {Operator State Bound}
    {dataSet : Five.FiveChannelFormBoundData Operator State Bound}
    {budget : Sixteenth.SixteenthBudgetAlgebra Bound} →
  (radius : FiveChannelSmallFieldRadius dataSet budget) →
  Five.LessEqual dataSet
    (Five.epsilonChart dataSet)
    (Sixteenth.oneSixteenth budget)
chartBelowSixteenth {dataSet = dataSet} radius =
  Five.transitive dataSet
    (chartLinearEstimate radius)
    (chartRadiusTarget radius)

gaugeBelowSixteenth :
  ∀ {Operator State Bound}
    {dataSet : Five.FiveChannelFormBoundData Operator State Bound}
    {budget : Sixteenth.SixteenthBudgetAlgebra Bound} →
  (radius : FiveChannelSmallFieldRadius dataSet budget) →
  Five.LessEqual dataSet
    (Five.epsilonGauge dataSet)
    (Sixteenth.oneSixteenth budget)
gaugeBelowSixteenth {dataSet = dataSet} radius =
  Five.transitive dataSet
    (gaugeLinearEstimate radius)
    (gaugeRadiusTarget radius)

constraintBelowSixteenth :
  ∀ {Operator State Bound}
    {dataSet : Five.FiveChannelFormBoundData Operator State Bound}
    {budget : Sixteenth.SixteenthBudgetAlgebra Bound} →
  (radius : FiveChannelSmallFieldRadius dataSet budget) →
  Five.LessEqual dataSet
    (Five.epsilonConstraint dataSet)
    (Sixteenth.oneSixteenth budget)
constraintBelowSixteenth {dataSet = dataSet} radius =
  Five.transitive dataSet
    (constraintLinearEstimate radius)
    (constraintRadiusTarget radius)

asFiveChannelSixteenthAllocation :
  ∀ {Operator State Bound}
    {dataSet : Five.FiveChannelFormBoundData Operator State Bound}
    {budget : Sixteenth.SixteenthBudgetAlgebra Bound} →
  FiveChannelSmallFieldRadius dataSet budget →
  Sixteenth.FiveChannelSixteenthAllocation dataSet
asFiveChannelSixteenthAllocation {budget = budget} radius = record
  { budget = budget
  ; physicalNestedFiveMeaning =
      physicalNestedFiveMeaning radius
  ; physicalFiveBelowHalf =
      physicalFiveBelowHalf radius
  ; curvatureBelowSixteenth =
      curvatureBelowSixteenth radius
  ; transportBelowSixteenth =
      transportBelowSixteenth radius
  ; chartBelowSixteenth =
      chartBelowSixteenth radius
  ; gaugeBelowSixteenth =
      gaugeBelowSixteenth radius
  ; constraintBelowSixteenth =
      constraintBelowSixteenth radius
  }

fiveChannelLinearRadiusReductionLevel : ProofLevel
fiveChannelLinearRadiusReductionLevel = machineChecked

fiveChannelRadiusAllocationAdapterLevel : ProofLevel
fiveChannelRadiusAllocationAdapterLevel = machineChecked

physicalFiveChannelLinearConstantsInputsLevel : ProofLevel
physicalFiveChannelLinearConstantsInputsLevel = conditional

physicalCommonSmallFieldRadiusInputsLevel : ProofLevel
physicalCommonSmallFieldRadiusInputsLevel = conditional
