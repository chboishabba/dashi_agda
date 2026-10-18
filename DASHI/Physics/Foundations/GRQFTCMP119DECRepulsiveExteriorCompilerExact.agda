{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTCMP119DECRepulsiveExteriorCompilerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Foundations.GRQFTRationalStressComponentCutExact as Stress
import DASHI.Physics.Foundations.GRQFTVacuumStressLambdaCompilerExact as Vacuum
import DASHI.Physics.Foundations.GRQFTGeneralIsraelDECCompatibleShellExact as Shell
import DASHI.Physics.Foundations.GRQFTRationalSquareIsraelDesignExact as Design

------------------------------------------------------------------------
-- CMP119 -> DEC-COMPATIBLE REPULSIVE EXTERIOR COMPILER
--
-- Once the existing normalized CMP119 stress equality is paid, the same tensor
-- can be rescaled to BOTH sides of the general Israel shell:
--
--   Lambda_out = 3/8
--   Lambda_in  = 21/64.
--
-- These amplitudes are not arbitrary in this fixture; they are exactly the
-- values derived from the rational square lapses
--
--   sqrt(f_out)=1/2
--   sqrt(f_in)=3/4.
------------------------------------------------------------------------

exteriorAmplitude : ℚ
exteriorAmplitude = Shell.lambdaOut

interiorAmplitude : ℚ
interiorAmplitude = Shell.lambdaIn

exteriorAmplitudeDerivedFromSquareLapse :
  exteriorAmplitude
    ≡ Design.lambdaOutFromSquareLapse
        Shell.mass Shell.radius Shell.sqrtFOut
exteriorAmplitudeDerivedFromSquareLapse = refl

interiorAmplitudeDerivedFromSquareLapse :
  interiorAmplitude
    ≡ Design.lambdaInFromSquareLapse
        Shell.radius Shell.sqrtFIn
interiorAmplitudeDerivedFromSquareLapse = refl

exteriorStress :
  Stress.RationalTensor4
exteriorStress =
  Vacuum.vacuumStressAt exteriorAmplitude

interiorStress :
  Stress.RationalTensor4
interiorStress =
  Vacuum.vacuumStressAt interiorAmplitude

exteriorStress00 :
  exteriorStress Flat.timeAxis Flat.timeAxis ≡ Int.+ 3 / 8
exteriorStress00 = refl

exteriorStress11 :
  exteriorStress Flat.xAxis Flat.xAxis ≡ - (Int.+ 3 / 8)
exteriorStress11 = refl

interiorStress00 :
  interiorStress Flat.timeAxis Flat.timeAxis ≡ Int.+ 21 / 64
interiorStress00 = refl

interiorStress11 :
  interiorStress Flat.xAxis Flat.xAxis ≡ - (Int.+ 21 / 64)
interiorStress11 = refl

------------------------------------------------------------------------
-- CMP119 TRANSPORT TO BOTH AMPLITUDES
------------------------------------------------------------------------

cmp119CompilesExteriorStress :
  ∀ {StressTensor : Set}
    {evaluator : Stress.CMP119RationalStressComponentEvaluator StressTensor}
    {cmp119Stress : StressTensor} →
  Stress.NormalizedCrossSectorStressInstance
    StressTensor evaluator cmp119Stress →
  (a b : Flat.Axis4) →
  exteriorStress a b
    ≡ Vacuum.scaledCMP119Tensor
        exteriorAmplitude evaluator cmp119Stress a b
cmp119CompilesExteriorStress instance =
  Vacuum.normalizedCMP119ScalesToVacuumStress
    instance exteriorAmplitude

cmp119CompilesInteriorStress :
  ∀ {StressTensor : Set}
    {evaluator : Stress.CMP119RationalStressComponentEvaluator StressTensor}
    {cmp119Stress : StressTensor} →
  Stress.NormalizedCrossSectorStressInstance
    StressTensor evaluator cmp119Stress →
  (a b : Flat.Axis4) →
  interiorStress a b
    ≡ Vacuum.scaledCMP119Tensor
        interiorAmplitude evaluator cmp119Stress a b
cmp119CompilesInteriorStress instance =
  Vacuum.normalizedCMP119ScalesToVacuumStress
    instance interiorAmplitude

------------------------------------------------------------------------
-- CONDITIONAL MAX-CUT
------------------------------------------------------------------------

record CMP119DECRepulsiveExteriorCompiler
    {StressTensor : Set}
    (evaluator : Stress.CMP119RationalStressComponentEvaluator StressTensor)
    (cmp119Stress : StressTensor)
    (normalized :
      Stress.NormalizedCrossSectorStressInstance
        StressTensor evaluator cmp119Stress) : Set where
  constructor cmp119-dec-repulsive-exterior-compiler
  field
    shellWitness :
      Shell.GeneralIsraelDECCompatibleShellWitness

    exteriorAmplitudeValue :
      exteriorAmplitude ≡ Int.+ 3 / 8

    interiorAmplitudeValue :
      interiorAmplitude ≡ Int.+ 21 / 64

    exteriorStressTransport :
      (a b : Flat.Axis4) →
      exteriorStress a b
        ≡ Vacuum.scaledCMP119Tensor
            exteriorAmplitude evaluator cmp119Stress a b

    interiorStressTransport :
      (a b : Flat.Axis4) →
      interiorStress a b
        ≡ Vacuum.scaledCMP119Tensor
            interiorAmplitude evaluator cmp119Stress a b

open CMP119DECRepulsiveExteriorCompiler public

cmp119DECRepulsiveExteriorCompiler :
  ∀ {StressTensor : Set}
    {evaluator : Stress.CMP119RationalStressComponentEvaluator StressTensor}
    {cmp119Stress : StressTensor} →
  (normalized :
    Stress.NormalizedCrossSectorStressInstance
      StressTensor evaluator cmp119Stress) →
  CMP119DECRepulsiveExteriorCompiler
    evaluator cmp119Stress normalized
cmp119DECRepulsiveExteriorCompiler normalized =
  cmp119-dec-repulsive-exterior-compiler
    Shell.canonicalGeneralIsraelDECCompatibleShellWitness
    refl
    refl
    (cmp119CompilesExteriorStress normalized)
    (cmp119CompilesInteriorStress normalized)

record CMP119DECRepulsiveExteriorCompilerBoundary : Set where
  constructor cmp119-dec-repulsive-exterior-compiler-boundary
  field
    oneNormalizedCMP119TensorFeedsBothRegions : Bool
    secondTensorWeldRequired : Bool
    exteriorAmplitudeDerivedFromJunctionGeometry : Bool
    interiorAmplitudeDerivedFromJunctionGeometry : Bool
    decCompatibleRepulsiveShellConstructed : Bool
    qftAmplitudeDynamicsConstructed : Bool
    physicalStressUnitsCalibrated : Bool

canonicalCMP119DECRepulsiveExteriorCompilerBoundary :
  CMP119DECRepulsiveExteriorCompilerBoundary
canonicalCMP119DECRepulsiveExteriorCompilerBoundary =
  cmp119-dec-repulsive-exterior-compiler-boundary
    true false true true true false false
