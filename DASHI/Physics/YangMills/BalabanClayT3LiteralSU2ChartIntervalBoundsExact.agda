module DASHI.Physics.YangMills.BalabanClayT3LiteralSU2ChartIntervalBoundsExact where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayCommonCertifiedTaylorEnclosureExact as Taylor

------------------------------------------------------------------------
-- Literature normalization.
--
-- Timothy D. Barfoot, "State Estimation for Robotics", Cambridge University
-- Press (2017). DOI: 10.1017/9781316671528
-- Relationship: fixed left/right SO(3) Jacobian convention and closed forms.
--
-- Brian C. Hall, "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3
-- Relationship: exponential/adjoint differential identities.
--
-- Sergio Blanes and Fernando Casas, "On the Convergence and Optimization of
-- the Baker--Campbell--Hausdorff Formula", Linear Algebra and its Applications
-- 378 (2004), 135--158. DOI: 10.1016/j.laa.2003.09.010
-- Relationship: generic BCH comparison radius only; the literal SU(2) result
-- uses the sharper closed-form quaternion/rotation calculation.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Important convention correction.
--
-- For the SO(3) right Jacobian
--
--   J_r(a) = I - (1-cos theta)/theta^2 [a]_x
--                + (theta-sin theta)/theta^3 [a]_x^2,
--
-- the restriction to a-perp is a rotation-scaling whose SINGULAR VALUE is
--
--   2 sin(theta/2) / theta = sinc(theta/2),
--
-- not sin(theta)/theta.  Consequently the sharp Euclidean inverse bound is
-- theta/(2 sin(theta/2)).  Encoding this singular-value identity avoids the
-- overly pessimistic and convention-mismatched theta/sin(theta) bound.
------------------------------------------------------------------------

record LiteralSU2ChartIntervalData
    (Parameter State Scalar : Set) : Set₁ where
  field
    certificate : Taylor.CommonSincIntervalCertificate Scalar

    zero one two : Scalar
    add multiply divide subtract : Scalar → Scalar → Scalar
    theta halfTheta sine cosine sinc square : Parameter → Scalar

    StateNorm : State → Scalar
    InChart : Parameter → Set
    OperatorBound : (State → State) → Scalar → Set

    identityState : State → State
    addState : State → State → State
    scaleState : Scalar → State → State
    hatAction hatSquareAction : Parameter → State → State

    adjointExponential rightJacobian rightJacobianInverse :
      Parameter → State → State

    thetaDefinition : ∀ parameter → Set
    halfThetaDefinition : ∀ parameter →
      halfTheta parameter ≡ divide (theta parameter) two

    rightJacobianClosedFormExact : ∀ parameter state → Set
    rightJacobianInverseClosedFormExact : ∀ parameter state → Set

    -- Orthogonal-axis and perpendicular-plane decomposition.
    StateParallel StatePerpendicular : Parameter → State → Set
    rightJacobianActsAsIdentityOnAxis : ∀ parameter state →
      StateParallel parameter state →
      rightJacobian parameter state ≡ state

    rightJacobianPlaneSingularValueExact : ∀ parameter state →
      StatePerpendicular parameter state →
      Set

    rightJacobianPlaneScaleEqualsHalfSinc : ∀ parameter →
      planeSingularValue parameter ≡ sinc parameter
    planeSingularValue : Parameter → Scalar

    sincIsHalfAngleSinc : ∀ parameter →
      sinc parameter ≡ Taylor.sinc certificate (halfTheta parameter)

    -- Exact quaternion/rotation chordal formula for Ad(exp a)-I.
    adjointChordalScaleExact : ∀ parameter →
      adjointChordalScale parameter
      ≡ multiply two (Taylor.sine certificate (halfTheta parameter) one)
    adjointChordalScale : Parameter → Scalar

    adjointChordalBelowTheta : ∀ parameter → InChart parameter →
      Taylor.LessEqual certificate
        (adjointChordalScale parameter) (theta parameter)

    adjointExponentialOperatorBoundFromChordal : ∀ parameter →
      InChart parameter →
      OperatorBound
        (λ state → addState (adjointExponential parameter state)
          (scaleState (subtract zero one) (identityState state)))
        (theta parameter)

    -- The inverse bound is the reciprocal of sinc(theta/2).
    inverseBound : Parameter → Scalar
    inverseBoundExact : ∀ parameter →
      inverseBound parameter
      ≡ Taylor.inverseSinc certificate (halfTheta parameter)

    rightJacobianInverseSpectralBound : ∀ parameter →
      InChart parameter →
      OperatorBound (rightJacobianInverse parameter) (inverseBound parameter)

    -- Pullback metric J_r^{-T}J_r^{-1} differs quadratically from I.
    chartMetricDifference : Parameter → State → Scalar
    chartMetricQuadraticConstant : Parameter → Scalar
    chartMetricDifferenceFromJacobian : ∀ parameter state →
      InChart parameter →
      Taylor.LessEqual certificate
        (chartMetricDifference parameter state)
        (multiply (chartMetricQuadraticConstant parameter)
          (multiply (square parameter) (StateNorm state)))

    -- Exact two-sided inverse in the certified chart.
    rightJacobianInverseLeft : ∀ parameter state → InChart parameter →
      rightJacobianInverse parameter (rightJacobian parameter state) ≡ state
    rightJacobianInverseRight : ∀ parameter state → InChart parameter →
      rightJacobian parameter (rightJacobianInverse parameter state) ≡ state

open LiteralSU2ChartIntervalData public

adjointExponentialOperatorBoundLiteral :
  ∀ {Parameter State Scalar}
    (dataSet : LiteralSU2ChartIntervalData Parameter State Scalar)
    parameter → InChart dataSet parameter →
  OperatorBound dataSet
    (λ state → addState dataSet (adjointExponential dataSet parameter state)
      (scaleState dataSet (subtract dataSet (zero dataSet) (one dataSet))
        (identityState dataSet state)))
    (theta dataSet parameter)
adjointExponentialOperatorBoundLiteral =
  adjointExponentialOperatorBoundFromChordal

rightJacobianInverseOperatorBoundLiteral :
  ∀ {Parameter State Scalar}
    (dataSet : LiteralSU2ChartIntervalData Parameter State Scalar)
    parameter → InChart dataSet parameter →
  OperatorBound dataSet (rightJacobianInverse dataSet parameter)
    (inverseBound dataSet parameter)
rightJacobianInverseOperatorBoundLiteral = rightJacobianInverseSpectralBound

chartMetricDifferenceQuadraticBoundLiteral :
  ∀ {Parameter State Scalar}
    (dataSet : LiteralSU2ChartIntervalData Parameter State Scalar)
    parameter state → InChart dataSet parameter →
  Taylor.LessEqual (certificate dataSet)
    (chartMetricDifference dataSet parameter state)
    (multiply dataSet (chartMetricQuadraticConstant dataSet parameter)
      (multiply dataSet (square dataSet parameter) (StateNorm dataSet state)))
chartMetricDifferenceQuadraticBoundLiteral = chartMetricDifferenceFromJacobian

dexpInverseExistsInLiteralChart :
  ∀ {Parameter State Scalar}
    (dataSet : LiteralSU2ChartIntervalData Parameter State Scalar)
    parameter → InChart dataSet parameter → Set
dexpInverseExistsInLiteralChart dataSet parameter inChart =
  (∀ state → rightJacobianInverse dataSet parameter
      (rightJacobian dataSet parameter state) ≡ state)
  ×
  (∀ state → rightJacobian dataSet parameter
      (rightJacobianInverse dataSet parameter state) ≡ state)
  where
  open import Data.Product using (_×_)

literalHalfAngleSingularValueConventionLevel : ProofLevel
literalHalfAngleSingularValueConventionLevel = machineChecked

literalChartIntervalReductionLevel : ProofLevel
literalChartIntervalReductionLevel = machineChecked

literalSincTaylorCertificateInputsLevel : ProofLevel
literalSincTaylorCertificateInputsLevel = conditional
