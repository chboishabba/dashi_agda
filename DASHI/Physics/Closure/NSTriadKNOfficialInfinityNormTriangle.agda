module DASHI.Physics.Closure.NSTriadKNOfficialInfinityNormTriangle where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Agda.Builtin.Nat as BN
open import Data.Integer.Base using (ℤ; _+_; -_; _-_ ; ∣_∣)
open import Data.Nat.Base using (_≤_; _⊔_)
import Data.Nat.Properties as Nat
import Data.Integer.Properties as Int
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical

------------------------------------------------------------------------
-- Exact cutoff-independent max-coordinate norm geometry on Z^3.
------------------------------------------------------------------------

max3 : Nat → Nat → Nat → Nat
max3 x y z = (x ⊔ y) ⊔ z

infinityNorm : Z3.FourierMode → Nat
infinityNorm k =
  max3
    (∣ Z3.kx k ∣)
    (∣ Z3.ky k ∣)
    (∣ Z3.kz k ∣)

first≤max3 : ∀ x y z → x ≤ max3 x y z
first≤max3 x y z =
  Nat.≤-trans
    (Nat.m≤m⊔n x y)
    (Nat.m≤m⊔n (x ⊔ y) z)

second≤max3 : ∀ x y z → y ≤ max3 x y z
second≤max3 x y z =
  Nat.≤-trans
    (Nat.n≤m⊔n x y)
    (Nat.m≤m⊔n (x ⊔ y) z)

third≤max3 : ∀ x y z → z ≤ max3 x y z
third≤max3 x y z = Nat.n≤m⊔n (x ⊔ y) z

max3Least :
  ∀ {x y z bound} →
  x ≤ bound → y ≤ bound → z ≤ bound →
  max3 x y z ≤ bound
max3Least x≤ y≤ z≤ =
  Nat.⊔-least (Nat.⊔-least x≤ y≤) z≤

xMagnitude≤InfinityNorm :
  ∀ k → ∣ Z3.kx k ∣ ≤ infinityNorm k
xMagnitude≤InfinityNorm k =
  first≤max3 (∣ Z3.kx k ∣) (∣ Z3.ky k ∣) (∣ Z3.kz k ∣)

yMagnitude≤InfinityNorm :
  ∀ k → ∣ Z3.ky k ∣ ≤ infinityNorm k
yMagnitude≤InfinityNorm k =
  second≤max3 (∣ Z3.kx k ∣) (∣ Z3.ky k ∣) (∣ Z3.kz k ∣)

zMagnitude≤InfinityNorm :
  ∀ k → ∣ Z3.kz k ∣ ≤ infinityNorm k
zMagnitude≤InfinityNorm k =
  third≤max3 (∣ Z3.kx k ∣) (∣ Z3.ky k ∣) (∣ Z3.kz k ∣)

coordinateSumBound :
  ∀ (coordinateP coordinateQ : ℤ) (boundP boundQ : Nat) →
  ∣ coordinateP ∣ ≤ boundP →
  ∣ coordinateQ ∣ ≤ boundQ →
  ∣ coordinateP + coordinateQ ∣ ≤ BN._+_ boundP boundQ
coordinateSumBound coordinateP coordinateQ boundP boundQ p≤ q≤ =
  Nat.≤-trans
    (Int.∣i+j∣≤∣i∣+∣j∣ coordinateP coordinateQ)
    (Nat.+-mono-≤ p≤ q≤)

infinityNormTriangle :
  ∀ p q →
  infinityNorm (Z3.addMode p q)
  ≤ BN._+_ (infinityNorm p) (infinityNorm q)
infinityNormTriangle p q =
  max3Least
    (coordinateSumBound
      (Z3.kx p) (Z3.kx q)
      (infinityNorm p) (infinityNorm q)
      (xMagnitude≤InfinityNorm p)
      (xMagnitude≤InfinityNorm q))
    (coordinateSumBound
      (Z3.ky p) (Z3.ky q)
      (infinityNorm p) (infinityNorm q)
      (yMagnitude≤InfinityNorm p)
      (yMagnitude≤InfinityNorm q))
    (coordinateSumBound
      (Z3.kz p) (Z3.kz q)
      (infinityNorm p) (infinityNorm q)
      (zMagnitude≤InfinityNorm p)
      (zMagnitude≤InfinityNorm q))

sumMinusLeft : ∀ i j → (i + j) - i ≡ j
sumMinusLeft i j =
  trans
    (cong (_+ (- i)) (Int.+-comm i j))
    (trans
      (Int.+-assoc j i (- i))
      (trans
        (cong (j +_) (Int.+-inverseʳ i))
        (Int.+-identityʳ j)))

coordinateReverseLeft :
  ∀ (coordinateP coordinateQ : ℤ) (boundSum boundQ : Nat) →
  ∣ coordinateP + coordinateQ ∣ ≤ boundSum →
  ∣ coordinateQ ∣ ≤ boundQ →
  ∣ coordinateP ∣ ≤ BN._+_ boundSum boundQ
coordinateReverseLeft coordinateP coordinateQ boundSum boundQ sum≤ q≤ =
  subst
    (λ magnitude → magnitude ≤ BN._+_ boundSum boundQ)
    (cong ∣_∣ (sumMinusLeft coordinateQ coordinateP))
    (Nat.≤-trans
      (Int.∣i-j∣≤∣i∣+∣j∣
        (coordinateQ + coordinateP)
        coordinateQ)
      (Nat.+-mono-≤
        (subst
          (λ magnitude → magnitude ≤ boundSum)
          (sym (cong ∣_∣ (Int.+-comm coordinateQ coordinateP)))
          sum≤)
        q≤))

infinityNormReverseLeft :
  ∀ p q →
  infinityNorm p
  ≤ BN._+_ (infinityNorm (Z3.addMode p q)) (infinityNorm q)
infinityNormReverseLeft p q =
  max3Least
    (coordinateReverseLeft
      (Z3.kx p) (Z3.kx q)
      (infinityNorm (Z3.addMode p q))
      (infinityNorm q)
      (xMagnitude≤InfinityNorm (Z3.addMode p q))
      (xMagnitude≤InfinityNorm q))
    (coordinateReverseLeft
      (Z3.ky p) (Z3.ky q)
      (infinityNorm (Z3.addMode p q))
      (infinityNorm q)
      (yMagnitude≤InfinityNorm (Z3.addMode p q))
      (yMagnitude≤InfinityNorm q))
    (coordinateReverseLeft
      (Z3.kz p) (Z3.kz q)
      (infinityNorm (Z3.addMode p q))
      (infinityNorm q)
      (zMagnitude≤InfinityNorm (Z3.addMode p q))
      (zMagnitude≤InfinityNorm q))

addModeCommutative : ∀ p q → Z3.addMode p q ≡ Z3.addMode q p
addModeCommutative (Z3.mode px py pz) (Z3.mode qx qy qz)
  rewrite Int.+-comm px qx
        | Int.+-comm py qy
        | Int.+-comm pz qz
  = refl

infinityNormReverseRight :
  ∀ p q →
  infinityNorm q
  ≤ BN._+_ (infinityNorm (Z3.addMode p q)) (infinityNorm p)
infinityNormReverseRight p q =
  subst
    (λ output →
      infinityNorm q ≤ BN._+_ (infinityNorm output) (infinityNorm p))
    (sym (addModeCommutative p q))
    (infinityNormReverseLeft q p)

record OfficialResonantNormConsequences
    (τ : Physical.PhysicalTriadIncidence) : Set where
  constructor official-resonant-norm-consequences
  field
    outputTriangle :
      infinityNorm (Physical.k τ)
      ≤ BN._+_ (infinityNorm (Physical.p τ)) (infinityNorm (Physical.q τ))

    pReverseTriangle :
      infinityNorm (Physical.p τ)
      ≤ BN._+_ (infinityNorm (Physical.k τ)) (infinityNorm (Physical.q τ))

    qReverseTriangle :
      infinityNorm (Physical.q τ)
      ≤ BN._+_ (infinityNorm (Physical.k τ)) (infinityNorm (Physical.p τ))

open OfficialResonantNormConsequences public

officialResonantNormConsequences :
  (τ : Physical.PhysicalTriadIncidence) →
  OfficialResonantNormConsequences τ
officialResonantNormConsequences τ =
  official-resonant-norm-consequences
    (subst
      (λ output →
        infinityNorm output
        ≤ BN._+_ (infinityNorm (Physical.p τ)) (infinityNorm (Physical.q τ)))
      (Physical.resonance τ)
      (infinityNormTriangle (Physical.p τ) (Physical.q τ)))
    (subst
      (λ output →
        infinityNorm (Physical.p τ)
        ≤ BN._+_ (infinityNorm output) (infinityNorm (Physical.q τ)))
      (Physical.resonance τ)
      (infinityNormReverseLeft (Physical.p τ) (Physical.q τ)))
    (subst
      (λ output →
        infinityNorm (Physical.q τ)
        ≤ BN._+_ (infinityNorm output) (infinityNorm (Physical.p τ)))
      (Physical.resonance τ)
      (infinityNormReverseRight (Physical.p τ) (Physical.q τ)))

officialInfinityNormTriangleClosed : Bool
officialInfinityNormTriangleClosed = true

officialInfinityNormTriangleClosedIsTrue :
  officialInfinityNormTriangleClosed ≡ true
officialInfinityNormTriangleClosedIsTrue = refl

dyadicIndexConsequenceConstantsClosed : Bool
dyadicIndexConsequenceConstantsClosed = false

dyadicIndexConsequenceConstantsClosedIsFalse :
  dyadicIndexConsequenceConstantsClosed ≡ false
dyadicIndexConsequenceConstantsClosedIsFalse = refl
