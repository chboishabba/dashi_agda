{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTCMP119NambuGotoRepulsiveExteriorCompilerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Foundations.GRQFTRationalStressComponentCutExact as Stress
import DASHI.Physics.Foundations.GRQFTVacuumStressLambdaCompilerExact as Vacuum

------------------------------------------------------------------------
-- CMP119 COMPILER FOR THE R=2 NAMBU-GOTO REPULSIVE BUBBLE
--
-- Required vacuum amplitudes:
--
--   interior = 21/64
--   exterior = 19/48.
--
-- One normalized CMP119 stress tensor feeds both by scalar multiplication.
------------------------------------------------------------------------

interiorAmplitude : ℚ
interiorAmplitude = Int.+ 21 / 64

exteriorAmplitude : ℚ
exteriorAmplitude = Int.+ 19 / 48

interiorStress : Stress.RationalTensor4
interiorStress =
  Vacuum.vacuumStressAt interiorAmplitude

exteriorStress : Stress.RationalTensor4
exteriorStress =
  Vacuum.vacuumStressAt exteriorAmplitude

interior00 :
  interiorStress Flat.timeAxis Flat.timeAxis ≡ Int.+ 21 / 64
interior00 = refl

interior11 :
  interiorStress Flat.xAxis Flat.xAxis ≡ - (Int.+ 21 / 64)
interior11 = refl

exterior00 :
  exteriorStress Flat.timeAxis Flat.timeAxis ≡ Int.+ 19 / 48
exterior00 = refl

exterior11 :
  exteriorStress Flat.xAxis Flat.xAxis ≡ - (Int.+ 19 / 48)
exterior11 = refl

cmp119CompilesNambuInteriorStress :
  ∀ {StressTensor : Set}
    {evaluator : Stress.CMP119RationalStressComponentEvaluator StressTensor}
    {cmp119Stress : StressTensor} →
  Stress.NormalizedCrossSectorStressInstance
    StressTensor evaluator cmp119Stress →
  (a b : Flat.Axis4) →
  interiorStress a b
    ≡ Vacuum.scaledCMP119Tensor
        interiorAmplitude evaluator cmp119Stress a b
cmp119CompilesNambuInteriorStress instance =
  Vacuum.normalizedCMP119ScalesToVacuumStress
    instance interiorAmplitude

cmp119CompilesNambuExteriorStress :
  ∀ {StressTensor : Set}
    {evaluator : Stress.CMP119RationalStressComponentEvaluator StressTensor}
    {cmp119Stress : StressTensor} →
  Stress.NormalizedCrossSectorStressInstance
    StressTensor evaluator cmp119Stress →
  (a b : Flat.Axis4) →
  exteriorStress a b
    ≡ Vacuum.scaledCMP119Tensor
        exteriorAmplitude evaluator cmp119Stress a b
cmp119CompilesNambuExteriorStress instance =
  Vacuum.normalizedCMP119ScalesToVacuumStress
    instance exteriorAmplitude

record CMP119NambuGotoRepulsiveExteriorCompiler
    {StressTensor : Set}
    (evaluator : Stress.CMP119RationalStressComponentEvaluator StressTensor)
    (cmp119Stress : StressTensor)
    (normalized :
      Stress.NormalizedCrossSectorStressInstance
        StressTensor evaluator cmp119Stress) : Set where
  constructor cmp119-nambu-goto-repulsive-exterior-compiler
  field
    interiorAmplitudeValue :
      interiorAmplitude ≡ Int.+ 21 / 64

    exteriorAmplitudeValue :
      exteriorAmplitude ≡ Int.+ 19 / 48

    interiorTransport :
      (a b : Flat.Axis4) →
      interiorStress a b
        ≡ Vacuum.scaledCMP119Tensor
            interiorAmplitude evaluator cmp119Stress a b

    exteriorTransport :
      (a b : Flat.Axis4) →
      exteriorStress a b
        ≡ Vacuum.scaledCMP119Tensor
            exteriorAmplitude evaluator cmp119Stress a b

open CMP119NambuGotoRepulsiveExteriorCompiler public

cmp119NambuGotoRepulsiveExteriorCompiler :
  ∀ {StressTensor : Set}
    {evaluator : Stress.CMP119RationalStressComponentEvaluator StressTensor}
    {cmp119Stress : StressTensor} →
  (normalized :
    Stress.NormalizedCrossSectorStressInstance
      StressTensor evaluator cmp119Stress) →
  CMP119NambuGotoRepulsiveExteriorCompiler
    evaluator cmp119Stress normalized
cmp119NambuGotoRepulsiveExteriorCompiler normalized =
  cmp119-nambu-goto-repulsive-exterior-compiler
    refl
    refl
    (cmp119CompilesNambuInteriorStress normalized)
    (cmp119CompilesNambuExteriorStress normalized)

record CMP119NambuGotoCompilerBoundary : Set where
  constructor cmp119-nambu-goto-compiler-boundary
  field
    oneNormalizedCMP119TensorFeedsBothRegions : Bool
    interiorAmplitudeExact : Bool
    exteriorAmplitudeExact : Bool
    additionalTensorWeldRequired : Bool
    sourceNativeAmplitudePotentialDerived : Bool

canonicalCMP119NambuGotoCompilerBoundary :
  CMP119NambuGotoCompilerBoundary
canonicalCMP119NambuGotoCompilerBoundary =
  cmp119-nambu-goto-compiler-boundary
    true true true false false
