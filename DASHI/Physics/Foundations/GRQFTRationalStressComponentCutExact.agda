{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTRationalStressComponentCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; +_; -[1+_]; 0ℚ; _+_; _-_)
open import Data.Nat.Base using (zero)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Closure.DiscreteWarpedEinsteinMatterModel as FiniteGR

------------------------------------------------------------------------
-- COMPONENTWISE NORMALIZED STRESS CARRIER
--
-- This is deliberately a normalized rational diagnostic carrier.  It does not
-- assert SI units or a physical value of 8*pi*G.  It exists so the first
-- cross-sector GRQFT comparison can be an executable 4x4 residual rather than
-- an opaque equality between abstract stress objects.
------------------------------------------------------------------------

RationalTensor4 : Set
RationalTensor4 = Flat.Axis4 → Flat.Axis4 → ℚ

sourceCoefficientToRational : FiniteGR.SourceCoefficient → ℚ
sourceCoefficientToRational FiniteGR.negativeSource = -[1+ zero ]
sourceCoefficientToRational FiniteGR.zeroSource = 0ℚ
sourceCoefficientToRational FiniteGR.positiveSource = + 1

finiteGRStressRational : RationalTensor4
finiteGRStressRational a b =
  sourceCoefficientToRational (FiniteGR.computedMatterStress a b)

finiteGREinsteinRational : RationalTensor4
finiteGREinsteinRational a b =
  sourceCoefficientToRational (FiniteGR.computedEinsteinTensor a b)

finiteGRStressEqualsEinsteinRational :
  (a b : Flat.Axis4) →
  finiteGRStressRational a b ≡ finiteGREinsteinRational a b
finiteGRStressEqualsEinsteinRational a b =
  cong sourceCoefficientToRational
    (sym (FiniteGR.computedEinsteinEqualsMatterStress a b))

finiteGR00 :
  finiteGRStressRational Flat.timeAxis Flat.timeAxis ≡ + 1
finiteGR00 = refl

finiteGR11 :
  finiteGRStressRational Flat.xAxis Flat.xAxis ≡ -[1+ zero ]
finiteGR11 = refl

finiteGR22 :
  finiteGRStressRational Flat.yAxis Flat.yAxis ≡ -[1+ zero ]
finiteGR22 = refl

finiteGR33 :
  finiteGRStressRational Flat.zAxis Flat.zAxis ≡ -[1+ zero ]
finiteGR33 = refl

finiteGR01 :
  finiteGRStressRational Flat.timeAxis Flat.xAxis ≡ 0ℚ
finiteGR01 = refl

finiteGR02 :
  finiteGRStressRational Flat.timeAxis Flat.yAxis ≡ 0ℚ
finiteGR02 = refl

finiteGR03 :
  finiteGRStressRational Flat.timeAxis Flat.zAxis ≡ 0ℚ
finiteGR03 = refl

finiteGR10 :
  finiteGRStressRational Flat.xAxis Flat.timeAxis ≡ 0ℚ
finiteGR10 = refl

finiteGR12 :
  finiteGRStressRational Flat.xAxis Flat.yAxis ≡ 0ℚ
finiteGR12 = refl

finiteGR13 :
  finiteGRStressRational Flat.xAxis Flat.zAxis ≡ 0ℚ
finiteGR13 = refl

finiteGR20 :
  finiteGRStressRational Flat.yAxis Flat.timeAxis ≡ 0ℚ
finiteGR20 = refl

finiteGR21 :
  finiteGRStressRational Flat.yAxis Flat.xAxis ≡ 0ℚ
finiteGR21 = refl

finiteGR23 :
  finiteGRStressRational Flat.yAxis Flat.zAxis ≡ 0ℚ
finiteGR23 = refl

finiteGR30 :
  finiteGRStressRational Flat.zAxis Flat.timeAxis ≡ 0ℚ
finiteGR30 = refl

finiteGR31 :
  finiteGRStressRational Flat.zAxis Flat.xAxis ≡ 0ℚ
finiteGR31 = refl

finiteGR32 :
  finiteGRStressRational Flat.zAxis Flat.yAxis ≡ 0ℚ
finiteGR32 = refl

stressResidual :
  RationalTensor4 →
  RationalTensor4 →
  RationalTensor4
stressResidual gr qft a b = gr a b - qft a b

record CMP119RationalStressComponentEvaluator
    (StressTensor : Set) : Set₁ where
  field
    component :
      StressTensor → Flat.Axis4 → Flat.Axis4 → ℚ

open CMP119RationalStressComponentEvaluator public

record NormalizedCrossSectorStressInstance
    (StressTensor : Set)
    (evaluator : CMP119RationalStressComponentEvaluator StressTensor)
    (cmp119Stress : StressTensor) : Set where
  field
    qft00 : component evaluator cmp119Stress Flat.timeAxis Flat.timeAxis ≡ + 1
    qft11 : component evaluator cmp119Stress Flat.xAxis Flat.xAxis ≡ -[1+ zero ]
    qft22 : component evaluator cmp119Stress Flat.yAxis Flat.yAxis ≡ -[1+ zero ]
    qft33 : component evaluator cmp119Stress Flat.zAxis Flat.zAxis ≡ -[1+ zero ]

    qft01 : component evaluator cmp119Stress Flat.timeAxis Flat.xAxis ≡ 0ℚ
    qft02 : component evaluator cmp119Stress Flat.timeAxis Flat.yAxis ≡ 0ℚ
    qft03 : component evaluator cmp119Stress Flat.timeAxis Flat.zAxis ≡ 0ℚ
    qft10 : component evaluator cmp119Stress Flat.xAxis Flat.timeAxis ≡ 0ℚ
    qft12 : component evaluator cmp119Stress Flat.xAxis Flat.yAxis ≡ 0ℚ
    qft13 : component evaluator cmp119Stress Flat.xAxis Flat.zAxis ≡ 0ℚ
    qft20 : component evaluator cmp119Stress Flat.yAxis Flat.timeAxis ≡ 0ℚ
    qft21 : component evaluator cmp119Stress Flat.yAxis Flat.xAxis ≡ 0ℚ
    qft23 : component evaluator cmp119Stress Flat.yAxis Flat.zAxis ≡ 0ℚ
    qft30 : component evaluator cmp119Stress Flat.zAxis Flat.timeAxis ≡ 0ℚ
    qft31 : component evaluator cmp119Stress Flat.zAxis Flat.xAxis ≡ 0ℚ
    qft32 : component evaluator cmp119Stress Flat.zAxis Flat.yAxis ≡ 0ℚ

open NormalizedCrossSectorStressInstance public

normalizedCMP119ComponentEvaluatorStillRequired : Bool
normalizedCMP119ComponentEvaluatorStillRequired = true

normalizedCMP119ComponentEvaluatorStillRequiredIsTrue :
  normalizedCMP119ComponentEvaluatorStillRequired ≡ true
normalizedCMP119ComponentEvaluatorStillRequiredIsTrue = refl

finiteGRComponentTargetAlreadyExecutable : Bool
finiteGRComponentTargetAlreadyExecutable = true

finiteGRComponentTargetAlreadyExecutableIsTrue :
  finiteGRComponentTargetAlreadyExecutable ≡ true
finiteGRComponentTargetAlreadyExecutableIsTrue = refl

physicalSIStressCalibrationClaimed : Bool
physicalSIStressCalibrationClaimed = false

physicalSIStressCalibrationClaimedIsFalse :
  physicalSIStressCalibrationClaimed ≡ false
physicalSIStressCalibrationClaimedIsFalse = refl
