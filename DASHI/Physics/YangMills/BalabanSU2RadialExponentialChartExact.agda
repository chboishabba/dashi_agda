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
------------------------------------------------------------------------

radialQuaternionNormExact : ∀ cosine scale x y z →
  qNormSqR cosine (scale *R x) (scale *R y) (scale *R z)
  ≡ squareR cosine +R (squareR scale *R vectorNormSqR x y z)
radialQuaternionNormExact =
  solveComputed 5
    (λ cosine scale x y z →
      qNormSqP cosine (scale :* x) (scale :* y) (scale :* z)
      := squareP cosine :+ (squareP scale :* vectorNormSqP x y z))
    computed

radialImaginaryNormExact : ∀ scale x y z →
  imaginaryNormSqR (scale *R x) (scale *R y) (scale *R z)
  ≡ squareR scale *R vectorNormSqR x y z
radialImaginaryNormExact =
  solveComputed 4
    (λ scale x y z →
      imaginaryNormSqP (scale :* x) (scale :* y) (scale :* z)
      := squareP scale :* vectorNormSqP x y z)
    computed

record SU2RadialExponentialChartData (radius : ℝ) : Set₁ where
  field
    radialOrderLaws : SU2AdjointSquaredRadiusOrderLaws

    radialParameter : Set
    radialParameterX radialParameterY radialParameterZ : radialParameter → ℝ
    radialCosine radialScale : radialParameter → ℝ
    radialInChartBall : radialParameter → Set

    radialUnitIdentity : ∀ parameter →
      radialInChartBall parameter →
      squareR (radialCosine parameter)
        +R (squareR (radialScale parameter)
          *R vectorNormSqR
            (radialParameterX parameter)
            (radialParameterY parameter)
            (radialParameterZ parameter))
      ≡ oneR

    radialImaginarySqBelowRadiusSq : ∀ parameter →
      radialInChartBall parameter →
      LessEqual (orderedSquares radialOrderLaws)
        (squareR (radialScale parameter)
          *R vectorNormSqR
            (radialParameterX parameter)
            (radialParameterY parameter)
            (radialParameterZ parameter))
        (squareR radius)

open SU2RadialExponentialChartData public

radialExpReal : ∀ {radius}
  (dataSet : SU2RadialExponentialChartData radius) →
  radialParameter dataSet → ℝ
radialExpReal dataSet = radialCosine dataSet

radialExpI : ∀ {radius}
  (dataSet : SU2RadialExponentialChartData radius) →
  radialParameter dataSet → ℝ
radialExpI dataSet parameter =
  radialScale dataSet parameter *R radialParameterX dataSet parameter

radialExpJ : ∀ {radius}
  (dataSet : SU2RadialExponentialChartData radius) →
  radialParameter dataSet → ℝ
radialExpJ dataSet parameter =
  radialScale dataSet parameter *R radialParameterY dataSet parameter

radialExpK : ∀ {radius}
  (dataSet : SU2RadialExponentialChartData radius) →
  radialParameter dataSet → ℝ
radialExpK dataSet parameter =
  radialScale dataSet parameter *R radialParameterZ dataSet parameter

radialExponentialUnitQuaternion :
  ∀ {radius} (dataSet : SU2RadialExponentialChartData radius)
    (parameter : radialParameter dataSet) →
  radialInChartBall dataSet parameter →
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
      (radialParameterX dataSet parameter)
      (radialParameterY dataSet parameter)
      (radialParameterZ dataSet parameter))
    (radialUnitIdentity dataSet parameter inBall)

radialExponentialImaginarySqBelowRadiusSq :
  ∀ {radius} (dataSet : SU2RadialExponentialChartData radius)
    (parameter : radialParameter dataSet) →
  radialInChartBall dataSet parameter →
  LessEqual (orderedSquares (radialOrderLaws dataSet))
    (imaginaryNormSqR
      (radialExpI dataSet parameter)
      (radialExpJ dataSet parameter)
      (radialExpK dataSet parameter))
    (squareR radius)
radialExponentialImaginarySqBelowRadiusSq dataSet parameter inBall
  rewrite radialImaginaryNormExact
    (radialScale dataSet parameter)
    (radialParameterX dataSet parameter)
    (radialParameterY dataSet parameter)
    (radialParameterZ dataSet parameter) =
  radialImaginarySqBelowRadiusSq dataSet parameter inBall

radialDataToPointwiseExponentialMatch :
  ∀ {radius} (dataSet : SU2RadialExponentialChartData radius) →
  SU2ExponentialPointwiseRadiusMatch radius
radialDataToPointwiseExponentialMatch dataSet = record
  { radiusOrderLaws = radialOrderLaws dataSet
  ; chartParameter = radialParameter dataSet
  ; expReal = radialExpReal dataSet
  ; expI = radialExpI dataSet
  ; expJ = radialExpJ dataSet
  ; expK = radialExpK dataSet
  ; inChartBall = radialInChartBall dataSet
  ; exponentialUnitQuaternion = radialExponentialUnitQuaternion dataSet
  ; exponentialImaginarySqBelowRadiusSq =
      radialExponentialImaginarySqBelowRadiusSq dataSet
  }

radialExponentialAdjointDisplacementRadiusSq :
  ∀ {radius} (dataSet : SU2RadialExponentialChartData radius) →
  ∀ (parameter : radialParameter dataSet) x y z →
  radialInChartBall dataSet parameter →
  LessEqual (orderedSquares (radialOrderLaws dataSet))
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
