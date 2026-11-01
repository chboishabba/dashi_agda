module DASHI.Physics.Foundations.FiniteUltrametricReebFlowExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.ProbabilityDecoratedReebExact as Reeb

------------------------------------------------------------------------
-- Finite depth-two ternary addresses.  Distance level records the first place
-- at which two addresses differ, giving a finite ultrametric analogue.

data Trit : Set where
  tritZero : Trit
  tritOne : Trit
  tritTwo : Trit

Address2 : Set
Address2 = Trit × Trit

data DistanceLevel : Set where
  distanceZero : DistanceLevel
  distanceNear : DistanceLevel
  distanceFar : DistanceLevel

sameTrit : Trit → Trit → Bool
sameTrit tritZero tritZero = true
sameTrit tritZero tritOne = false
sameTrit tritZero tritTwo = false
sameTrit tritOne tritZero = false
sameTrit tritOne tritOne = true
sameTrit tritOne tritTwo = false
sameTrit tritTwo tritZero = false
sameTrit tritTwo tritOne = false
sameTrit tritTwo tritTwo = true

addressDistance : Address2 → Address2 → DistanceLevel
addressDistance (a0 , a1) (b0 , b1) with sameTrit a0 b0
... | false = distanceFar
... | true with sameTrit a1 b1
...   | false = distanceNear
...   | true = distanceZero

addressA : Address2
addressA = tritZero , tritZero

addressB : Address2
addressB = tritZero , tritOne

addressC : Address2
addressC = tritTwo , tritOne

addressAIsNearB : addressDistance addressA addressB ≡ distanceNear
addressAIsNearB = refl

addressAIsFarFromC : addressDistance addressA addressC ≡ distanceFar
addressAIsFarFromC = refl

addressBIsFarFromC : addressDistance addressB addressC ≡ distanceFar
addressBIsFarFromC = refl

------------------------------------------------------------------------
-- Local chart and hierarchical address are retained as a product rather than
-- identified.

data LocalChartPoint : Set where
  localLeft : LocalChartPoint
  localCentre : LocalChartPoint
  localRight : LocalChartPoint

record HybridState : Set where
  constructor hybridState
  field
    localCoordinate : LocalChartPoint
    hierarchicalAddress : Address2

open HybridState public

canonicalHybridState : HybridState
canonicalHybridState = hybridState localCentre addressB

------------------------------------------------------------------------
-- Finite transition weights on the Reeb graph.  Each split and merge row has
-- common denominator six and the outgoing weights sum to six.

transitionWeight : Reeb.ReebEdge → Nat
transitionWeight Reeb.sourceToLeft = 2
transitionWeight Reeb.sourceToRight = 4
transitionWeight Reeb.leftToMerge = 6
transitionWeight Reeb.rightToMerge = 6

splitRowNormalisesToSix :
  transitionWeight Reeb.sourceToLeft
  +
  transitionWeight Reeb.sourceToRight
  ≡
  6
splitRowNormalisesToSix = refl

leftMergeRowNormalisesToSix :
  transitionWeight Reeb.leftToMerge ≡ 6
leftMergeRowNormalisesToSix = refl

rightMergeRowNormalisesToSix :
  transitionWeight Reeb.rightToMerge ≡ 6
rightMergeRowNormalisesToSix = refl

------------------------------------------------------------------------
-- History weights are products of edge weights.  This is an unnormalised
-- finite path measure, not a quantum amplitude.

data ReebHistory : Set where
  leftHistory : ReebHistory
  rightHistory : ReebHistory

historyWeight : ReebHistory → Nat
historyWeight leftHistory =
  transitionWeight Reeb.sourceToLeft
  *
  transitionWeight Reeb.leftToMerge
historyWeight rightHistory =
  transitionWeight Reeb.sourceToRight
  *
  transitionWeight Reeb.rightToMerge

leftHistoryWeightIsTwelve : historyWeight leftHistory ≡ 12
leftHistoryWeightIsTwelve = refl

rightHistoryWeightIsTwentyFour : historyWeight rightHistory ≡ 24
rightHistoryWeightIsTwentyFour = refl

------------------------------------------------------------------------
-- Temporal thickness is an interval label attached to a transition, not an
-- instantaneous topological point.

data TemporalThickness : Set where
  oneTickThick : TemporalThickness
  twoTicksThick : TemporalThickness
  threeTicksThick : TemporalThickness

edgeThickness : Reeb.ReebEdge → TemporalThickness
edgeThickness Reeb.sourceToLeft = twoTicksThick
edgeThickness Reeb.sourceToRight = twoTicksThick
edgeThickness Reeb.leftToMerge = oneTickThick
edgeThickness Reeb.rightToMerge = oneTickThick

splitTransitionsHaveEqualThickness :
  edgeThickness Reeb.sourceToLeft
  ≡
  edgeThickness Reeb.sourceToRight
splitTransitionsHaveEqualThickness = refl

------------------------------------------------------------------------
-- A declared topological current combines source mass and transition weight.

weightedCurrent : Reeb.ReebNode → Reeb.ReebEdge → Nat
weightedCurrent node edge = Reeb.massBefore node * transitionWeight edge

sourceToLeftCurrentIsTwelve :
  weightedCurrent Reeb.sourceComponent Reeb.sourceToLeft ≡ 12
sourceToLeftCurrentIsTwelve = refl

sourceToRightCurrentIsTwentyFour :
  weightedCurrent Reeb.sourceComponent Reeb.sourceToRight ≡ 24
sourceToRightCurrentIsTwentyFour = refl

record FiniteUltrametricReebFlowBoundary : Set where
  constructor finiteUltrametricReebFlowBoundary
  field
    ultrametricAddressIsSmoothSpatialCoordinate : Bool
    ultrametricAddressIsSmoothSpatialCoordinateIsFalse :
      ultrametricAddressIsSmoothSpatialCoordinate ≡ false

    normalisedFiniteTransitionWeightsAreQuantumAmplitudes : Bool
    normalisedFiniteTransitionWeightsAreQuantumAmplitudesIsFalse :
      normalisedFiniteTransitionWeightsAreQuantumAmplitudes ≡ false

    temporalThicknessSuppliesRelativisticProperTime : Bool
    temporalThicknessSuppliesRelativisticProperTimeIsFalse :
      temporalThicknessSuppliesRelativisticProperTime ≡ false

    arbitrarySlicingIsRelativisticallyAdmissible : Bool
    arbitrarySlicingIsRelativisticallyAdmissibleIsFalse :
      arbitrarySlicingIsRelativisticallyAdmissible ≡ false

    reebFlowForcesThreeSixNineThresholds : Bool
    reebFlowForcesThreeSixNineThresholdsIsFalse :
      reebFlowForcesThreeSixNineThresholds ≡ false

open FiniteUltrametricReebFlowBoundary public

canonicalFiniteUltrametricReebFlowBoundary :
  FiniteUltrametricReebFlowBoundary
canonicalFiniteUltrametricReebFlowBoundary =
  finiteUltrametricReebFlowBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
