{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTVacuumStressLambdaCompilerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _/_; _*_; -_)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Foundations.GRQFTRationalStressComponentCutExact as Stress
import DASHI.Physics.Foundations.GRQFTDeSitterKottlerJunctionExact as Junction

------------------------------------------------------------------------
-- RATIONAL LORENTZ METRIC AND VACUUM-STRESS RAY
--
-- In the declared (-,+,+,+) frame:
--
--   g = diag(-1,+1,+1,+1)
--   T^(1) = diag(+1,-1,-1,-1) = -g.
--
-- The existing finite GR stress tensor is exactly T^(1).
------------------------------------------------------------------------

rationalMetric : Stress.RationalTensor4
rationalMetric Flat.timeAxis Flat.timeAxis = - 1ℚ
rationalMetric Flat.timeAxis Flat.xAxis = 0ℚ
rationalMetric Flat.timeAxis Flat.yAxis = 0ℚ
rationalMetric Flat.timeAxis Flat.zAxis = 0ℚ
rationalMetric Flat.xAxis Flat.timeAxis = 0ℚ
rationalMetric Flat.xAxis Flat.xAxis = 1ℚ
rationalMetric Flat.xAxis Flat.yAxis = 0ℚ
rationalMetric Flat.xAxis Flat.zAxis = 0ℚ
rationalMetric Flat.yAxis Flat.timeAxis = 0ℚ
rationalMetric Flat.yAxis Flat.xAxis = 0ℚ
rationalMetric Flat.yAxis Flat.yAxis = 1ℚ
rationalMetric Flat.yAxis Flat.zAxis = 0ℚ
rationalMetric Flat.zAxis Flat.timeAxis = 0ℚ
rationalMetric Flat.zAxis Flat.xAxis = 0ℚ
rationalMetric Flat.zAxis Flat.yAxis = 0ℚ
rationalMetric Flat.zAxis Flat.zAxis = 1ℚ

negativeMetric : Stress.RationalTensor4
negativeMetric a b = - (rationalMetric a b)

finiteGRStressIsNegativeMetric :
  (a b : Flat.Axis4) →
  Stress.finiteGRStressRational a b ≡ negativeMetric a b
finiteGRStressIsNegativeMetric Flat.timeAxis Flat.timeAxis = refl
finiteGRStressIsNegativeMetric Flat.timeAxis Flat.xAxis = refl
finiteGRStressIsNegativeMetric Flat.timeAxis Flat.yAxis = refl
finiteGRStressIsNegativeMetric Flat.timeAxis Flat.zAxis = refl
finiteGRStressIsNegativeMetric Flat.xAxis Flat.timeAxis = refl
finiteGRStressIsNegativeMetric Flat.xAxis Flat.xAxis = refl
finiteGRStressIsNegativeMetric Flat.xAxis Flat.yAxis = refl
finiteGRStressIsNegativeMetric Flat.xAxis Flat.zAxis = refl
finiteGRStressIsNegativeMetric Flat.yAxis Flat.timeAxis = refl
finiteGRStressIsNegativeMetric Flat.yAxis Flat.xAxis = refl
finiteGRStressIsNegativeMetric Flat.yAxis Flat.yAxis = refl
finiteGRStressIsNegativeMetric Flat.yAxis Flat.zAxis = refl
finiteGRStressIsNegativeMetric Flat.zAxis Flat.timeAxis = refl
finiteGRStressIsNegativeMetric Flat.zAxis Flat.xAxis = refl
finiteGRStressIsNegativeMetric Flat.zAxis Flat.yAxis = refl
finiteGRStressIsNegativeMetric Flat.zAxis Flat.zAxis = refl

------------------------------------------------------------------------
-- SCALAR AMPLITUDE FAMILY
--
-- Under normalized kappa=1, the source
--
--   T^(lambda)_munu = -lambda g_munu
--
-- is exactly the cosmological-stress source corresponding to effective
-- Lambda=lambda when the cosmological term is moved to the source side.
------------------------------------------------------------------------

scaleTensor :
  ℚ → Stress.RationalTensor4 → Stress.RationalTensor4
scaleTensor amplitude tensor a b =
  amplitude * tensor a b

vacuumStressAt :
  ℚ → Stress.RationalTensor4
vacuumStressAt amplitude =
  scaleTensor amplitude Stress.finiteGRStressRational

vacuumStressIsMinusLambdaMetric :
  (amplitude : ℚ) →
  (a b : Flat.Axis4) →
  vacuumStressAt amplitude a b
    ≡ amplitude * negativeMetric a b
vacuumStressIsMinusLambdaMetric amplitude a b =
  cong (λ x → amplitude * x)
    (finiteGRStressIsNegativeMetric a b)

effectiveLambdaFromVacuumStress :
  ℚ → ℚ
effectiveLambdaFromVacuumStress amplitude = amplitude

vacuumStressAmplitudeCompilesToLambda :
  (amplitude : ℚ) →
  effectiveLambdaFromVacuumStress amplitude ≡ amplitude
vacuumStressAmplitudeCompilesToLambda amplitude = refl

------------------------------------------------------------------------
-- THE JUNCTION AMPLITUDES ARE THE SAME STRESS RAY
------------------------------------------------------------------------

interiorVacuumStress :
  Stress.RationalTensor4
interiorVacuumStress =
  vacuumStressAt Junction.lambdaIn

exteriorVacuumStress :
  Stress.RationalTensor4
exteriorVacuumStress =
  vacuumStressAt Junction.lambdaOut

interiorLambdaDerivedFromStressAmplitude :
  effectiveLambdaFromVacuumStress Junction.lambdaIn
    ≡ Int.+ 3 / 8
interiorLambdaDerivedFromStressAmplitude = refl

exteriorLambdaDerivedFromStressAmplitude :
  effectiveLambdaFromVacuumStress Junction.lambdaOut
    ≡ Int.+ 3 / 16
exteriorLambdaDerivedFromStressAmplitude = refl

interior00 :
  interiorVacuumStress Flat.timeAxis Flat.timeAxis
    ≡ Int.+ 3 / 8
interior00 = refl

interior11 :
  interiorVacuumStress Flat.xAxis Flat.xAxis
    ≡ - (Int.+ 3 / 8)
interior11 = refl

exterior00 :
  exteriorVacuumStress Flat.timeAxis Flat.timeAxis
    ≡ Int.+ 3 / 16
exterior00 = refl

exterior11 :
  exteriorVacuumStress Flat.xAxis Flat.xAxis
    ≡ - (Int.+ 3 / 16)
exterior11 = refl

------------------------------------------------------------------------
-- CMP119 TRANSPORT
--
-- Once a normalized CMP119 stress tensor has paid the existing sixteen
-- component equations, every scalar amplitude on the vacuum-stress ray follows
-- by congruence.  No second tensor-identification theorem is required for the
-- exterior Lambda carrier.
------------------------------------------------------------------------

scaledCMP119Tensor :
  ∀ {StressTensor : Set} →
  ℚ →
  Stress.CMP119RationalStressComponentEvaluator StressTensor →
  StressTensor →
  Stress.RationalTensor4
scaledCMP119Tensor amplitude evaluator stress a b =
  amplitude * Stress.component evaluator stress a b

normalizedCMP119ScalesToVacuumStress :
  ∀ {StressTensor : Set}
    {evaluator : Stress.CMP119RationalStressComponentEvaluator StressTensor}
    {cmp119Stress : StressTensor} →
  Stress.NormalizedCrossSectorStressInstance
    StressTensor evaluator cmp119Stress →
  (amplitude : ℚ) →
  (a b : Flat.Axis4) →
  vacuumStressAt amplitude a b
    ≡ scaledCMP119Tensor amplitude evaluator cmp119Stress a b
normalizedCMP119ScalesToVacuumStress instance amplitude a b =
  cong (λ x → amplitude * x)
    (Stress.normalizedSixteenComponentsCompileToTensorEquality instance a b)

normalizedCMP119CompilesExteriorLambdaStress :
  ∀ {StressTensor : Set}
    {evaluator : Stress.CMP119RationalStressComponentEvaluator StressTensor}
    {cmp119Stress : StressTensor} →
  Stress.NormalizedCrossSectorStressInstance
    StressTensor evaluator cmp119Stress →
  (a b : Flat.Axis4) →
  exteriorVacuumStress a b
    ≡ scaledCMP119Tensor Junction.lambdaOut evaluator cmp119Stress a b
normalizedCMP119CompilesExteriorLambdaStress instance =
  normalizedCMP119ScalesToVacuumStress instance Junction.lambdaOut

record VacuumStressLambdaCompilerBoundary : Set where
  constructor vacuum-stress-lambda-compiler-boundary
  field
    normalizedGRStressIsMinusMetric : Bool
    scalarStressAmplitudeCompilesToEffectiveLambda : Bool
    interiorAndExteriorUseSameVacuumStressRay : Bool
    junctionExteriorLambdaDerivedFromStressAmplitude : Bool
    cmp119NormalizedTensorScalesWithoutSecondTensorTheorem : Bool
    qftAmplitudeProducerConstructed : Bool
    SIStressCalibrationConstructed : Bool

canonicalVacuumStressLambdaCompilerBoundary :
  VacuumStressLambdaCompilerBoundary
canonicalVacuumStressLambdaCompilerBoundary =
  vacuum-stress-lambda-compiler-boundary
    true true true true true false false
