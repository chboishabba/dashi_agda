module DASHI.Physics.Closure.ExtremalFrobeniusClockCarrier where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Fin.Base using (Fin)
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.ExtremalFrobeniusOrbitArithmetic as Orbit

------------------------------------------------------------------------
-- Concrete finite clocks for the extremal 47/59/71 orbit bridge.

P47Clock : Set
P47Clock = Fin 47

P59Clock : Set
P59Clock = Fin 59

P71Clock : Set
P71Clock = Fin 71

ExtremalClockProduct : Set
ExtremalClockProduct =
  P47Clock × P59Clock × P71Clock

data ExtremalClockId : Set where
  p47Clock :
    ExtremalClockId

  p59Clock :
    ExtremalClockId

  p71Clock :
    ExtremalClockId

clockCarrier :
  ExtremalClockId →
  Set
clockCarrier p47Clock =
  P47Clock
clockCarrier p59Clock =
  P59Clock
clockCarrier p71Clock =
  P71Clock

clockPeriod :
  ExtremalClockId →
  Nat
clockPeriod p47Clock =
  47
clockPeriod p59Clock =
  59
clockPeriod p71Clock =
  71

combinedClockPeriod : Nat
combinedClockPeriod =
  clockPeriod p47Clock * clockPeriod p59Clock * clockPeriod p71Clock

p47-clock-period-is-47 :
  clockPeriod p47Clock ≡ 47
p47-clock-period-is-47 =
  refl

p59-clock-period-is-59 :
  clockPeriod p59Clock ≡ 59
p59-clock-period-is-59 =
  refl

p71-clock-period-is-71 :
  clockPeriod p71Clock ≡ 71
p71-clock-period-is-71 =
  refl

combined-clock-period-is-extremal-product :
  combinedClockPeriod ≡ Orbit.extremalProduct
combined-clock-period-is-extremal-product =
  refl

combined-clock-period-is-196883 :
  combinedClockPeriod ≡ 196883
combined-clock-period-is-196883 =
  Orbit.extremal-product-is-196883

record ExtremalFrobeniusClockCarrier : Set₁ where
  constructor extremalFrobeniusClockCarrier
  field
    p47Carrier :
      Set

    p59Carrier :
      Set

    p71Carrier :
      Set

    combinedCarrier :
      Set

    p47Period :
      Nat

    p59Period :
      Nat

    p71Period :
      Nat

    combinedPeriod :
      Nat

    p47PeriodIs47 :
      p47Period ≡ 47

    p59PeriodIs59 :
      p59Period ≡ 59

    p71PeriodIs71 :
      p71Period ≡ 71

    combinedPeriodIsProduct :
      combinedPeriod ≡ 47 * 59 * 71

    combinedPeriodIs196883 :
      combinedPeriod ≡ 196883

open ExtremalFrobeniusClockCarrier public

canonicalExtremalFrobeniusClockCarrier :
  ExtremalFrobeniusClockCarrier
canonicalExtremalFrobeniusClockCarrier =
  extremalFrobeniusClockCarrier
    P47Clock
    P59Clock
    P71Clock
    ExtremalClockProduct
    (clockPeriod p47Clock)
    (clockPeriod p59Clock)
    (clockPeriod p71Clock)
    combinedClockPeriod
    p47-clock-period-is-47
    p59-clock-period-is-59
    p71-clock-period-is-71
    refl
    combined-clock-period-is-196883
