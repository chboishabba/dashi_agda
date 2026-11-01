module DASHI.Algebra.MoonshineBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

import CRTPeriod as CRT
import JFixedPoint as J

moonshineCoefficient : Nat
moonshineCoefficient = 196884

crtPeriodPlusOne : CRT.period + 1 ≡ moonshineCoefficient
crtPeriodPlusOne = refl

jUnitContract : J.contract J.unit-obs ≡ moonshineCoefficient
jUnitContract = refl

MoonshineBridge :
  CRT.period + 1 ≡ J.contract J.unit-obs
MoonshineBridge = refl

record MoonshineScalarBridge : Set where
  constructor moonshineScalarBridge
  field
    periodPlusOne : CRT.period + 1 ≡ moonshineCoefficient
    unitContract : J.contract J.unit-obs ≡ moonshineCoefficient
    bridge : CRT.period + 1 ≡ J.contract J.unit-obs

moonshineScalarBridgeSurface : MoonshineScalarBridge
moonshineScalarBridgeSurface =
  moonshineScalarBridge
    crtPeriodPlusOne
    jUnitContract
    MoonshineBridge
