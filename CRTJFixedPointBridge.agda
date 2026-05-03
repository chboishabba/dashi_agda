module CRTJFixedPointBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

import CRTPeriod as CRT
import JFixedPoint as J

period-plus-one : CRT.period + 1 ≡ 196884
period-plus-one = refl

unit-contract-period-plus-one :
  J.contract J.unit-obs ≡ CRT.period + 1
unit-contract-period-plus-one = refl

stack-contract-period-plus-one :
  (n : Nat) →
  J.contract (J.stack n) ≡ CRT.period + 1
stack-contract-period-plus-one zero    = refl
stack-contract-period-plus-one (suc n) = refl

crt-periodicity-at-moonshine-minus-one :
  (k : Nat) →
  CRT.d (CRT.period + k * CRT.period) ≡ CRT.d CRT.period
crt-periodicity-at-moonshine-minus-one k =
  CRT.period-thm CRT.period k

record CRTJFixedPointBridge : Set where
  constructor crtJFixedPointBridge
  field
    crtPeriodPlusOne : CRT.period + 1 ≡ 196884
    unitContractMatchesPeriodPlusOne :
      J.contract J.unit-obs ≡ CRT.period + 1
    stackContractMatchesPeriodPlusOne :
      (n : Nat) →
      J.contract (J.stack n) ≡ CRT.period + 1
    moonshineMinusOnePeriodicity :
      (k : Nat) →
      CRT.d (CRT.period + k * CRT.period) ≡ CRT.d CRT.period

crtJFixedPointBridgeSurface : CRTJFixedPointBridge
crtJFixedPointBridgeSurface =
  crtJFixedPointBridge
    period-plus-one
    unit-contract-period-plus-one
    stack-contract-period-plus-one
    crt-periodicity-at-moonshine-minus-one
