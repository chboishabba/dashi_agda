module DASHI.Physics.YangMills.BalabanSU2RadialExponentialChartExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  (_+R_; _*R_; oneR)
open import DASHI.Physics.YangMills.BalabanSU2AdjointTransportExact
open import DASHI.Physics.YangMills.BalabanSU2AdjointPointwiseRadiusSquared
open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  (module RealPolynomialSolver)
open import DASHI.Physics.YangMills.BalabanComputedPolynomialSolver using
  (solveComputed; computed)
open RealPolynomialSolver using (_:=_; _:+_; _:*_)

------------------------------------------------------------------------
-- Exact radial algebra for the SU(2) exponential chart.
--
-- For a radial representation
--
--   q(A) = (c(A), s(A) A1, s(A) A2, s(A) A3),
--
-- quaternion unitarity and the imaginary-radius estimate reduce to two scalar
-- statements.  The vector/quaternion algebra below is proved computationally;
-- only the genuine analytic facts about c and s remain as named fields.
------------------------------------------------------------------------

radialQuaternionNormExact : ∀ cosine radialScale x y z →
  qNormSqR
    cosine
    (radialScale *R x)
    (radialScale *R y)
    (radialScale *R z)
  ≡ squareR cosine
    +R (squareR radialScale *R vectorNormSqR x y z)
radialQuaternionNormExact =
  solveComputed 5
    (λ cosine radialScale x y z →
      qNormSqP
        cosine
        (radialScale :* x)
        (radialScale :* y)
        (radialScale :* z)
      := squareP cosine
        :+ (squareP radialScale :* vectorNormSqP x y z))
    computed

radialImaginaryNormExact : ∀ radialScale x y z →
  imaginaryNormSqR
    (radialScale *R x)
    (radialScale *R y)
    (radialScale *R z)
  ≡ squareR radialScale *R vectorNormSqR x y z
radialImaginaryNormExact =
  solveComputed 4
    (λ radialScale x y z →
      imaginaryNormSqP
        (radialScale :* x)
        (radialScale :* y)
        (radialScale :* z)
      := squareP radialScale :* vectorNormSqP x y z)
    computed

record SU2RadialExponentialChartData (radius : ℝ) : Set₁ where
  field
    radiusOrderLaws : SU2AdjointSquaredRadiusOrderLaws

    chartParameter : Set
    parameterX parameterY parameterZ : chartParameter → ℝ
    radialCosine radialScale : chartParameter → ℝ
    inChartBall : chartParameter → Set

    radialUnitIdentity : ∀ parameter →
      inChartBall parameter →
      squareR (radialCosine parameter)
        +R (squareR (radialScale parameter)
          *R vectorNormSqR
            (parameterX parameter)
            (parameterY parameter)
            (parameterZ parameter))
      ≡ oneR

    radialImaginarySqBelowRadiusSq : ∀ parameter →
      inChartBall parameter →
      LessEqual (orderedSquares radiusOrderLaws)
        (squareR (radialScale parameter)
          *R vectorNormSqR
            (parameterX parameter)
            (parameterY parameter)
            (parameterZ parameter))
        (squareR radius)

open SU2RadialExponentialChartData public

radialExpReal : ∀ {radius}
  (dataSet : SU2RadialExponentialChartData radius) →
  chartParameter dataSet → ℝ
radialExpReal dataSet = radialCosine dataSet

radialExpI : ∀ {radius}
  (dataSet : SU2RadialExponentialChartData radius) →
  chartParameter dataSet → ℝ
radialExpI dataSet parameter =
  radialScale dataSet parameter *R parameterX dataSet parameter

radialExpJ : ∀ {radius}
  (dataSet : SU2RadialExponentialChartData radius) →
  chartParameter dataSet → ℝ
radialExpJ dataSet parameter =
  radialScale dataSet parameter *R parameterY dataSet parameter

radialExpK : ∀ {radius}
  (dataSet : SU2RadialExponentialChartData radius) →
  chartParameter dataSet → ℝ
radialExpK dataSet parameter =
  radialScale dataSet parameter *R parameterZ dataSet parameter

radialExponentialUnitQuaternion :
  ∀ {radius} (dataSet : SU2RadialExponentialChartData radius)
    (parameter : chartParameter dataSet) →
  inChartBall dataSet parameter →
  qNormSqR
    (radialExpReal dataSet parameter)
    (radialExpI dataSet parameter)
    (radialExpJ dataSet parameter)
    (radialExpK dataSet parameter)
  ≡ oneR
radialExponentialUnitQuaternion dataSet parameter inBall =
  trans
    (radialQuaternionNormExact
      (radialCosine dataSet parameter)
      (radialScale dataSet parameter)
      (parameterX dataSet parameter)
      (parameterY dataSet parameter)
      (parameterZ dataSet parameter))
    (radialUnitIdentity dataSet parameter inBall)

radialExponentialImaginarySqBelowRadiusSq :
  ∀ {radius} (dataSet : SU2RadialExponentialChartData radius)
    (parameter : chartParameter dataSet) →
  inChartBall dataSet parameter →
  LessEqual (orderedSquares (radiusOrderLaws dataSet))
    (imaginaryNormSqR
      (radialExpI dataSet parameter)
      (radialExpJ dataSet parameter)
      (radialExpK dataSet parameter))
    (squareR radius)
radialExponentialImaginarySqBelowRadiusSq dataSet parameter inBall
  rewrite radialImaginaryNormExact
    (radialScale dataSet parameter)
    (parameterX dataSet parameter)
    (parameterY dataSet parameter)
    (parameterZ dataSet parameter) =
  radialImaginarySqBelowRadiusSq dataSet parameter inBall

radialDataToPointwiseExponentialMatch :
  ∀ {radius} (dataSet : SU2RadialExponentialChartData radius) →
  SU2ExponentialPointwiseRadiusMatch radius
radialDataToPointwiseExponentialMatch dataSet = record
  { radiusOrderLaws = radiusOrderLaws dataSet
  ; chartParameter = chartParameter dataSet
  ; expReal = radialExpReal dataSet
  ; expI = radialExpI dataSet
  ; expJ = radialExpJ dataSet
  ; expK = radialExpK dataSet
  ; inChartBall = inChartBall dataSet
  ; exponentialUnitQuaternion =
      radialExponentialUnitQuaternion dataSet
  ; exponentialImaginarySqBelowRadiusSq =
      radialExponentialImaginarySqBelowRadiusSq dataSet
  }

radialExponentialAdjointDisplacementRadiusSq :
  ∀ {radius} (dataSet : SU2RadialExponentialChartData radius) →
  ∀ (parameter : chartParameter dataSet) x y z →
  inChartBall dataSet parameter →
  LessEqual (orderedSquares (radiusOrderLaws dataSet))
    (adjointDisplacementSqR
      (radialExpReal dataSet parameter)
      (radialExpI dataSet parameter)
      (radialExpJ dataSet parameter)
      (radialExpK dataSet parameter)
      x y z)
    (fourRadiusTimesVectorPointwiseR radius x y z)
radialExponentialAdjointDisplacementRadiusSq
  dataSet parameter x y z inBall =
  exponentialAdjointDisplacementRadiusSqPointwise
    (radialDataToPointwiseExponentialMatch dataSet)
    parameter x y z inBall

su2RadialQuaternionAlgebraLevel : ProofLevel
su2RadialQuaternionAlgebraLevel = computed

su2RadialExponentialChartReductionLevel : ProofLevel
su2RadialExponentialChartReductionLevel = machineChecked

su2RadialScalarUnitIdentityLevel : ProofLevel
su2RadialScalarUnitIdentityLevel = conditional

su2RadialScalarRadiusBoundLevel : ProofLevel
su2RadialScalarRadiusBoundLevel = conditional
