module DASHI.Physics.Closure.ExtremalFrobeniusOrbitArithmetic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Empty using (⊥)
open import Data.Nat.Coprimality using (Coprime)

import CRTPeriod as CRT
open import MonsterOntos public using (p47; p59; p71)
open import MonsterOntos using (SSP; toNat)
import DASHI.Arithmetic.TrackedCoprimeTable as CoprimeTable
import DASHI.Physics.CRTPeriodJFixedBridge as CRTBridge

------------------------------------------------------------------------
-- Extremal 47/59/71 arithmetic slice for the Frobenius orbit bridge.

extremalPrime47 : SSP
extremalPrime47 = p47

extremalPrime59 : SSP
extremalPrime59 = p59

extremalPrime71 : SSP
extremalPrime71 = p71

p47-nat : toNat p47 ≡ 47
p47-nat = CRTBridge.p47-nat

p59-nat : toNat p59 ≡ 59
p59-nat = CRTBridge.p59-nat

p71-nat : toNat p71 ≡ 71
p71-nat = CRTBridge.p71-nat

------------------------------------------------------------------------
-- Pairwise coprimality of the extremal tracked primes.

_≢_ : SSP → SSP → Set
p ≢ q = p ≡ q → ⊥

p47≢p59 : p47 ≢ p59
p47≢p59 ()

p47≢p71 : p47 ≢ p71
p47≢p71 ()

p59≢p71 : p59 ≢ p71
p59≢p71 ()

p47-p59-coprime : Coprime 47 59
p47-p59-coprime =
  CoprimeTable.distinctTrackedBasesCoprime p47 p59 p47≢p59

p47-p71-coprime : Coprime 47 71
p47-p71-coprime =
  CoprimeTable.distinctTrackedBasesCoprime p47 p71 p47≢p71

p59-p71-coprime : Coprime 59 71
p59-p71-coprime =
  CoprimeTable.distinctTrackedBasesCoprime p59 p71 p59≢p71

------------------------------------------------------------------------
-- Extremal product and CRT period.

extremalProduct : Nat
extremalProduct = 47 * 59 * 71

extremal-product-is-196883 :
  47 * 59 * 71 ≡ 196883
extremal-product-is-196883 = refl

crt-period-is-extremal-product :
  CRT.period ≡ extremalProduct
crt-period-is-extremal-product = CRTBridge.crt-period-prime-product

crt-period-is-196883 :
  CRT.period ≡ 196883
crt-period-is-196883 = refl
