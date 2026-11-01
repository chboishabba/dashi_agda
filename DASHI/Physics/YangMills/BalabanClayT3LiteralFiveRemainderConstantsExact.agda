module DASHI.Physics.YangMills.BalabanClayT3LiteralFiveRemainderConstantsExact where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT3LiteralBackgroundHessianRemaindersExact as Remainder
import DASHI.Physics.YangMills.BalabanClayT3LiteralSU2ChartIntervalBoundsExact as Chart

------------------------------------------------------------------------
-- Literature normalization.
--
-- Tadeusz Bałaban, "Propagators for Lattice Gauge Theories in a Background
-- Field", Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355
-- Relationship: background covariant derivative, local propagator and
-- random-walk comparison architecture.
--
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042
-- Relationship: nonlinear averaging/block-map regularity.
--
-- Timothy D. Barfoot, "State Estimation for Robotics", Cambridge University
-- Press (2017). DOI: 10.1017/9781316671528
-- Relationship: exact SO(3) Jacobian convention used by the chart term.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Primitive-to-five-term producer.
--
-- The old five-term record starts at the already-summed form bounds.  This
-- record names the geometric sources of those bounds so the constants can be
-- audited independently: plaquette incidence, transported edge differences,
-- chart pullback metric, covariant divergence, and block-path derivatives.
------------------------------------------------------------------------

record LiteralFiveRemainderConstantProducer
    (Background State Bound Parameter ChartState Scalar : Set) : Set₁ where
  field
    remainderData :
      Remainder.LiteralFiveBackgroundRemainderData Background State Bound
    chartData : Chart.LiteralSU2ChartIntervalData Parameter ChartState Scalar

    backgroundParameter : Background → Parameter
    chartState : State → ChartState

    -- Curvature/commutator lane.
    plaquetteCurvatureCommutatorBound : ∀ background state → Set
    backgroundCurvatureControlledByChartRadius : ∀ background →
      Remainder.BackgroundInRadius remainderData
        (Remainder.radius remainderData) background → Set
    plaquetteIncidenceBound : ∀ state → Set

    curvatureRemainderPointwiseBoundLiteral : ∀ background state →
      Remainder.BackgroundInRadius remainderData
        (Remainder.radius remainderData) background →
      Remainder.LessEqual remainderData
        (Remainder.curvatureRemainder remainderData background state)
        (Remainder.multiply remainderData
          (Remainder.curvatureCoefficient remainderData)
          (Remainder.multiply remainderData
            (Remainder.radius remainderData)
            (Remainder.normSq remainderData state)))

    -- Transport lane from the exact adjoint chordal bound.
    transportedForwardDifferenceExact : ∀ background state → Set
    transportedEdgeIncidenceBound : ∀ state → Set
    transportedDifferenceMinusDifferenceBoundLiteral : ∀ background state →
      Remainder.BackgroundInRadius remainderData
        (Remainder.radius remainderData) background →
      Remainder.LessEqual remainderData
        (Remainder.transportRemainder remainderData background state)
        (Remainder.multiply remainderData
          (Remainder.transportCoefficient remainderData)
          (Remainder.multiply remainderData
            (Remainder.radius remainderData)
            (Remainder.normSq remainderData state)))

    -- Chart metric lane from J_r^{-T}J_r^{-1}-I.
    chartPullbackMetricExact : ∀ background state → Set
    chartMetricDifferenceQuadraticBoundLiteral : ∀ background state →
      Remainder.BackgroundInRadius remainderData
        (Remainder.radius remainderData) background →
      Remainder.LessEqual remainderData
        (Remainder.chartRemainder remainderData background state)
        (Remainder.multiply remainderData
          (Remainder.chartCoefficient remainderData)
          (Remainder.multiply remainderData
            (Remainder.radius remainderData)
            (Remainder.normSq remainderData state)))

    -- Gauge lane.  Young's parameter is part of the explicit constant budget.
    covariantDivergenceDifferenceExact : ∀ background state → Set
    divergenceIncidenceBound : ∀ state → Set
    optimizedYoungParameter : Bound
    optimizedYoungInequality : ∀ background state → Set
    covariantDivergencePerturbationBoundLiteral : ∀ background state →
      Remainder.BackgroundInRadius remainderData
        (Remainder.radius remainderData) background →
      Remainder.LessEqual remainderData
        (Remainder.gaugeRemainder remainderData background state)
        (Remainder.multiply remainderData
          (Remainder.gaugeCoefficient remainderData)
          (Remainder.multiply remainderData
            (Remainder.radius remainderData)
            (Remainder.normSq remainderData state)))

    -- Nonlinear block derivative lane.
    blockPathLengthBound : Bound
    blockDerivativeTransportExpansionExact : ∀ background state → Set
    blockDerivativePathTelescopingBound : ∀ background state → Set
    blockDerivativeDifferencePointwiseBoundLiteral : ∀ background state →
      Remainder.BackgroundInRadius remainderData
        (Remainder.radius remainderData) background →
      Remainder.LessEqual remainderData
        (Remainder.constraintRemainder remainderData background state)
        (Remainder.multiply remainderData
          (Remainder.constraintCoefficient remainderData)
          (Remainder.multiply remainderData
            (Remainder.radius remainderData)
            (Remainder.normSq remainderData state)))

    -- Coefficient ownership.  The total is definitionally the sum of the five
    -- independently auditable constants.
    literalTotalCoefficientDefinition :
      Remainder.totalCoefficient remainderData
      ≡ Remainder.add remainderData
          (Remainder.curvatureCoefficient remainderData)
          (Remainder.add remainderData
            (Remainder.transportCoefficient remainderData)
            (Remainder.add remainderData
              (Remainder.chartCoefficient remainderData)
              (Remainder.add remainderData
                (Remainder.gaugeCoefficient remainderData)
                (Remainder.constraintCoefficient remainderData))))

open LiteralFiveRemainderConstantProducer public

curvatureRemainderRelativeBoundLiteral :
  ∀ {Background State Bound Parameter ChartState Scalar}
    (dataSet : LiteralFiveRemainderConstantProducer
      Background State Bound Parameter ChartState Scalar)
    background state →
  Remainder.BackgroundInRadius (remainderData dataSet)
    (Remainder.radius (remainderData dataSet)) background →
  Remainder.LessEqual (remainderData dataSet)
    (Remainder.curvatureRemainder (remainderData dataSet) background state)
    (Remainder.multiply (remainderData dataSet)
      (Remainder.curvatureCoefficient (remainderData dataSet))
      (Remainder.multiply (remainderData dataSet)
        (Remainder.radius (remainderData dataSet))
        (Remainder.normSq (remainderData dataSet) state)))
curvatureRemainderRelativeBoundLiteral = curvatureRemainderPointwiseBoundLiteral

transportRemainderRelativeBoundLiteral =
  transportedDifferenceMinusDifferenceBoundLiteral

chartRemainderRelativeBoundLiteral =
  chartMetricDifferenceQuadraticBoundLiteral

gaugeRemainderRelativeBoundLiteral =
  covariantDivergencePerturbationBoundLiteral

constraintRemainderRelativeBoundLiteral =
  blockDerivativeDifferencePointwiseBoundLiteral

literalFiveBackgroundRemainderBounds :
  ∀ {Background State Bound Parameter ChartState Scalar}
    (dataSet : LiteralFiveRemainderConstantProducer
      Background State Bound Parameter ChartState Scalar)
    background state →
  Remainder.BackgroundInRadius (remainderData dataSet)
    (Remainder.radius (remainderData dataSet)) background →
  Remainder.LessEqual (remainderData dataSet)
    (Remainder.totalRemainder (remainderData dataSet) background state)
    (Remainder.multiply (remainderData dataSet)
      (Remainder.totalCoefficient (remainderData dataSet))
      (Remainder.multiply (remainderData dataSet)
        (Remainder.radius (remainderData dataSet))
        (Remainder.normSq (remainderData dataSet) state)))
literalFiveBackgroundRemainderBounds dataSet =
  Remainder.backgroundHessianRemainderCommonRadiusBound (remainderData dataSet)

literalCurvatureConstantReductionLevel : ProofLevel
literalCurvatureConstantReductionLevel = machineChecked

literalTransportChartConstantReductionLevel : ProofLevel
literalTransportChartConstantReductionLevel = machineChecked

literalGaugeConstraintConstantReductionLevel : ProofLevel
literalGaugeConstraintConstantReductionLevel = machineChecked

literalFiveRemainderAssemblyLevel : ProofLevel
literalFiveRemainderAssemblyLevel = machineChecked

literalGeometricConstantInputsLevel : ProofLevel
literalGeometricConstantInputsLevel = conditional
