module DASHI.Physics.Foundations.ParameterInformationGeometryExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Finite information-geometric coordinate change.
--
-- Chart lambda uses tangent component 2 with metric weight 1.  Chart eta uses
-- tangent component 1 with metric weight 4.  Both represent the same tangent
-- norm, so the objective is attached to the theory-space point rather than to
-- a raw coordinate magnitude.

data ParameterChart : Set where
  lambdaChart : ParameterChart
  etaChart : ParameterChart

metricWeight : ParameterChart → Nat
metricWeight lambdaChart = 1
metricWeight etaChart = 4

tangentComponent : ParameterChart → Nat
tangentComponent lambdaChart = 2
tangentComponent etaChart = 1

tangentNormSquare : ParameterChart → Nat
tangentNormSquare chart =
  metricWeight chart
  *
  tangentComponent chart
  *
  tangentComponent chart

lambdaNormSquareIsFour : tangentNormSquare lambdaChart ≡ 4
lambdaNormSquareIsFour = refl

etaNormSquareIsFour : tangentNormSquare etaChart ≡ 4
etaNormSquareIsFour = refl

reparametrisedNormIsInvariant :
  tangentNormSquare lambdaChart ≡ tangentNormSquare etaChart
reparametrisedNormIsInvariant = refl

------------------------------------------------------------------------
-- Finite gradient-flow special case.  This is an example where a scalar
-- objective is a Lyapunov function for one declared RG step; it is not a
-- generic identification of MDL and RG.

data FlowPoint : Set where
  highLossPoint : FlowPoint
  lowLossPoint : FlowPoint
  fixedLossPoint : FlowPoint

flowStep : FlowPoint → FlowPoint
flowStep highLossPoint = lowLossPoint
flowStep lowLossPoint = fixedLossPoint
flowStep fixedLossPoint = fixedLossPoint

lyapunovValue : FlowPoint → Nat
lyapunovValue highLossPoint = 3
lyapunovValue lowLossPoint = 1
lyapunovValue fixedLossPoint = 0

highStepDecreasesLyapunov :
  lyapunovValue (flowStep highLossPoint)
  ≤
  lyapunovValue highLossPoint
highStepDecreasesLyapunov = s≤s z≤n

lowStepDecreasesLyapunov :
  lyapunovValue (flowStep lowLossPoint)
  ≤
  lyapunovValue lowLossPoint
lowStepDecreasesLyapunov = z≤n

fixedStepPreservesLyapunov :
  lyapunovValue (flowStep fixedLossPoint)
  ≡
  lyapunovValue fixedLossPoint
fixedStepPreservesLyapunov = refl

record ParameterInformationGeometryBoundary : Set where
  constructor parameterInformationGeometryBoundary
  field
    rawCoordinateMagnitudeIsInvariant : Bool
    rawCoordinateMagnitudeIsInvariantIsFalse :
      rawCoordinateMagnitudeIsInvariant ≡ false

    everyRGFlowIsGradientFlowOfMDL : Bool
    everyRGFlowIsGradientFlowOfMDLIsFalse :
      everyRGFlowIsGradientFlowOfMDL ≡ false

    finiteMetricExampleDerivesPhysicalFisherMetric : Bool
    finiteMetricExampleDerivesPhysicalFisherMetricIsFalse :
      finiteMetricExampleDerivesPhysicalFisherMetric ≡ false

open ParameterInformationGeometryBoundary public

canonicalParameterInformationGeometryBoundary :
  ParameterInformationGeometryBoundary
canonicalParameterInformationGeometryBoundary =
  parameterInformationGeometryBoundary false refl false refl false refl
