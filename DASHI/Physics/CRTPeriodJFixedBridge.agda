module DASHI.Physics.CRTPeriodJFixedBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

import CRTPeriod as CRT
import JFixedPoint as J
open import MonsterOntos using (p47; p59; p71; toNat)
import Ontology.GodelLattice as GL
import DASHI.Arithmetic.ActiveWallBounds as AWB
open import DASHI.Arithmetic.ArithmeticIntegerEmbedding using (Int)

crt-period-prime-product :
  CRT.period ≡ 47 * 59 * 71
crt-period-prime-product = refl

j-contract-period-plus-one :
  J.contract J.unit-obs ≡ CRT.period + 1
j-contract-period-plus-one = refl

p47-nat : toNat p47 ≡ 47
p47-nat = refl

p59-nat : toNat p59 ≡ 59
p59-nat = refl

p71-nat : toNat p71 ≡ 71
p71-nat = refl

activeWallScaled15-p47 :
  ∀ (x y : Int) →
  GL.Vec15.e47 (AWB.activeWallScaled15 x y)
    ≡ AWB.activeWallScaledAt p47 x y
activeWallScaled15-p47 x y = refl

activeWallScaled15-p59 :
  ∀ (x y : Int) →
  GL.Vec15.e59 (AWB.activeWallScaled15 x y)
    ≡ AWB.activeWallScaledAt p59 x y
activeWallScaled15-p59 x y = refl

activeWallScaled15-p71 :
  ∀ (x y : Int) →
  GL.Vec15.e71 (AWB.activeWallScaled15 x y)
    ≡ AWB.activeWallScaledAt p71 x y
activeWallScaled15-p71 x y = refl

W3 : Int → Int → Nat
W3 x y =
  AWB.activeWallScaledAt p47 x y +
  AWB.activeWallScaledAt p59 x y +
  AWB.activeWallScaledAt p71 x y

W3PeriodicityLaw : Set
W3PeriodicityLaw =
  ∀ x y k →
  W3 (x + k * CRT.period) y ≡ W3 x y

record W3PeriodicityObligation : Set where
  constructor mkW3PeriodicityObligation
  field
    periodicity : W3PeriodicityLaw

record MoonshineRepresentationObligation : Set where
  constructor moonshineRepresentationObligation
  field
    c1j : Nat
    c1j-is-196884 : c1j ≡ 196884
    smallestNontrivialMonsterIrrepDimension : Nat
    irrep-dimension-is-period :
      smallestNontrivialMonsterIrrepDimension ≡ CRT.period

record SSPMoonshineCoupling : Set₁ where
  constructor sspMoonshineCoupling
  field
    crtPeriodProduct : CRT.period ≡ 47 * 59 * 71
    jContractBridge : J.contract J.unit-obs ≡ CRT.period + 1
    p47Channel : toNat p47 ≡ 47
    p59Channel : toNat p59 ≡ 59
    p71Channel : toNat p71 ≡ 71
    activeWallP47 :
      ∀ x y →
      GL.Vec15.e47 (AWB.activeWallScaled15 x y)
        ≡ AWB.activeWallScaledAt p47 x y
    activeWallP59 :
      ∀ x y →
      GL.Vec15.e59 (AWB.activeWallScaled15 x y)
        ≡ AWB.activeWallScaledAt p59 x y
    activeWallP71 :
      ∀ x y →
      GL.Vec15.e71 (AWB.activeWallScaled15 x y)
        ≡ AWB.activeWallScaledAt p71 x y
    wallPressure3 : Int → Int → Nat
    wallPressure3Definition : ∀ x y → wallPressure3 x y ≡ W3 x y
    w3PeriodicityTarget : Set
    moonshineRepresentationTarget : Set

sspMoonshineCouplingSurface : SSPMoonshineCoupling
sspMoonshineCouplingSurface =
  sspMoonshineCoupling
    crt-period-prime-product
    j-contract-period-plus-one
    p47-nat
    p59-nat
    p71-nat
    activeWallScaled15-p47
    activeWallScaled15-p59
    activeWallScaled15-p71
    W3
    (λ x y → refl)
    W3PeriodicityObligation
    MoonshineRepresentationObligation
