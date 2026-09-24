{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTDECRepulsiveExteriorMaxCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Foundations.GRQFTRationalStressComponentCutExact as Stress
import DASHI.Physics.Foundations.GRQFTCMP119DECRepulsiveExteriorCompilerExact as CMP
import DASHI.Physics.Foundations.GRQFTVacuumStressLambdaCompilerExact as Vacuum
import DASHI.Physics.Foundations.GRQFTGeneralIsraelDECCompatibleShellExact as Shell
import DASHI.Physics.Foundations.GRQFTRationalSquareIsraelDesignExact as Design
import DASHI.Physics.Foundations.GRQFTBalancedDECRepulsiveShellFamilyExact as Family

------------------------------------------------------------------------
-- AUTHORITATIVE DEC-COMPATIBLE REPULSIVE EXTERIOR MAX-CUT
--
-- Geometry already selects:
--
--   Lambda_in  = 21/64
--   Lambda_out = 3/8
--
-- from the rational lapse roots x=3/4, y=1/2 at M=1/4, R=2.
--
-- One normalized CMP119 tensor then generates both stress tensors by scalar
-- multiplication.  The shell has positive surface energy, tangential tension,
-- NEC/WEC/DEC compatibility, SEC violation, and outward exterior acceleration.
--
-- The remaining source-native QFT theorem is to derive this two-level amplitude
-- structure from the actual CMP119/YM dynamics, not another tensor-shape identification.
------------------------------------------------------------------------

record GeometrySelectedVacuumAmplitudes : Set where
  constructor geometry-selected-vacuum-amplitudes
  field
    interiorAmplitude : ℚ
    exteriorAmplitude : ℚ

    interiorDerived :
      interiorAmplitude
        ≡ Design.lambdaInFromSquareLapse
            Shell.radius Shell.sqrtFIn

    exteriorDerived :
      exteriorAmplitude
        ≡ Design.lambdaOutFromSquareLapse
            Shell.mass Shell.radius Shell.sqrtFOut

    interiorValue :
      interiorAmplitude ≡ Int.+ 21 / 64

    exteriorValue :
      exteriorAmplitude ≡ Int.+ 3 / 8

open GeometrySelectedVacuumAmplitudes public

canonicalGeometrySelectedVacuumAmplitudes :
  GeometrySelectedVacuumAmplitudes
canonicalGeometrySelectedVacuumAmplitudes =
  geometry-selected-vacuum-amplitudes
    Shell.lambdaIn
    Shell.lambdaOut
    refl
    refl
    refl
    refl

------------------------------------------------------------------------
-- The still-open physical producer is explicitly scalar.
------------------------------------------------------------------------

record CMP119VacuumAmplitudeModelReceipt : Set where
  constructor cmp119-vacuum-amplitude-model-receipt
  field
    interiorAmplitudeProduced : ℚ
    exteriorAmplitudeProduced : ℚ

    interiorAmplitudeIsSelected :
      interiorAmplitudeProduced ≡ Int.+ 21 / 64

    exteriorAmplitudeIsSelected :
      exteriorAmplitudeProduced ≡ Int.+ 3 / 8

    sameVacuumStressRayHasTwoStableLevels : Set
    sameVacuumStressRayHasTwoStableLevelsEvidence :
      sameVacuumStressRayHasTwoStableLevels

open CMP119VacuumAmplitudeModelReceipt public

------------------------------------------------------------------------
-- MAX-CUT CONDITIONAL ONLY ON NORMALIZED TENSOR + AMPLITUDE DYNAMICS
------------------------------------------------------------------------

record DECRepulsiveExteriorMaxCut
    {StressTensor : Set}
    (evaluator : Stress.CMP119RationalStressComponentEvaluator StressTensor)
    (cmp119Stress : StressTensor)
    (normalized :
      Stress.NormalizedCrossSectorStressInstance
        StressTensor evaluator cmp119Stress)
    (amplitudes : CMP119VacuumAmplitudeModelReceipt) : Set where
  constructor dec-repulsive-exterior-max-cut
  field
    geometryAmplitudes :
      GeometrySelectedVacuumAmplitudes

    shell :
      Shell.GeneralIsraelDECCompatibleShellWitness

    compiler :
      CMP.CMP119DECRepulsiveExteriorCompiler
        evaluator cmp119Stress normalized

    producedInteriorAmplitude :
      interiorAmplitudeProduced amplitudes ≡ Int.+ 21 / 64

    producedExteriorAmplitude :
      exteriorAmplitudeProduced amplitudes ≡ Int.+ 3 / 8

    exteriorStressFromSameCMP119Ray :
      (a b : Flat.Axis4) →
      CMP.exteriorStress a b
        ≡ Vacuum.scaledCMP119Tensor
            CMP.exteriorAmplitude evaluator cmp119Stress a b

    interiorStressFromSameCMP119Ray :
      (a b : Flat.Axis4) →
      CMP.interiorStress a b
        ≡ Vacuum.scaledCMP119Tensor
            CMP.interiorAmplitude evaluator cmp119Stress a b

    outwardExteriorAcceleration :
      Shell.exteriorAcceleration ≡ Int.+ 3 / 16

    shellNECDECMargin :
      Shell.surfaceNECMargin8Pi ≡ Int.+ 1 / 24

    shellSECViolation :
      Shell.surfaceSECMargin8Pi ≡ - (Int.+ 1 / 6)

open DECRepulsiveExteriorMaxCut public

decRepulsiveExteriorMaxCut :
  ∀ {StressTensor : Set}
    {evaluator : Stress.CMP119RationalStressComponentEvaluator StressTensor}
    {cmp119Stress : StressTensor}
    {normalized :
      Stress.NormalizedCrossSectorStressInstance
        StressTensor evaluator cmp119Stress} →
  (amplitudes : CMP119VacuumAmplitudeModelReceipt) →
  DECRepulsiveExteriorMaxCut
    evaluator cmp119Stress normalized amplitudes
decRepulsiveExteriorMaxCut amplitudes =
  dec-repulsive-exterior-max-cut
    canonicalGeometrySelectedVacuumAmplitudes
    Shell.canonicalGeneralIsraelDECCompatibleShellWitness
    (CMP.cmp119DECRepulsiveExteriorCompiler normalized)
    (interiorAmplitudeIsSelected amplitudes)
    (exteriorAmplitudeIsSelected amplitudes)
    (CMP.cmp119CompilesExteriorStress normalized)
    (CMP.cmp119CompilesInteriorStress normalized)
    Shell.exteriorAccelerationIsThreeSixteenths
    Shell.surfaceNECMarginIsOneTwentyFourth
    Shell.surfaceSECMarginIsMinusOneSixth

record DECRepulsiveExteriorMaxCutBoundary : Set where
  constructor dec-repulsive-exterior-max-cut-boundary
  field
    geometrySelectsInteriorExteriorAmplitudes : Bool
    normalizedCMP119ShapeFeedsBothRegions : Bool
    decCompatiblePositiveEnergyShellConstructed : Bool
    outwardExteriorAccelerationConstructed : Bool
    negativeMetricMassRequired : Bool
    negativeNewtonGRequired : Bool
    additionalTensorWeldRequired : Bool
    sourceNativeQFTAmplitudeDerivationStillRequired : Bool
    SIStressCalibrationStillRequired : Bool

canonicalDECRepulsiveExteriorMaxCutBoundary :
  DECRepulsiveExteriorMaxCutBoundary
canonicalDECRepulsiveExteriorMaxCutBoundary =
  dec-repulsive-exterior-max-cut-boundary
    true true true true false false false true true
