module DASHI.Physics.Closure.NSTriadKNLuoPeriodicWalshCharacterOrthogonalityExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Classical finite Fourier analysis on the elementary abelian group
-- (Z/2Z)^3.  Repository-original Agda proof; no DOI is assigned.
--
-- Related references:
-- Author: Loukas Grafakos.
-- Title: "Classical Fourier Analysis".
-- DOI: 10.1007/978-1-4939-1194-3.
--
-- PURPOSE
-- Construct, rather than assume, a concrete three-dimensional periodic
-- character system.  On the eight-point torus (Z/2Z)^3 the Walsh characters
-- take values +/-1 and satisfy
--
--   sum_x chi_k(x) chi_l(x) = 8 delta_{k,l}.
--
-- This is an exact rational model of torus character orthogonality and a
-- checked finite Galerkin basis.  It does not identify the eight-point group
-- with the full continuous torus T^3; that passage remains a separate
-- analytic realization.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _/_; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality as Eq using (cong; sym; trans)
open Eq.≡-Reasoning

data Bit : Set where
  b0 b1 : Bit

data Bit3 : Set where
  bit3 : Bit → Bit → Bit → Bit3

minusOne two eight : ℚ
minusOne = - 1ℚ
two = Int.+ 2 / 1
eight = Int.+ 8 / 1

bitCharacter : Bit → Bit → ℚ
bitCharacter b0 point = 1ℚ
bitCharacter b1 b0 = 1ℚ
bitCharacter b1 b1 = minusOne

bitDelta : Bit → Bit → ℚ
bitDelta b0 b0 = 1ℚ
bitDelta b0 b1 = 0ℚ
bitDelta b1 b0 = 0ℚ
bitDelta b1 b1 = 1ℚ

oneDimPairSum : Bit → Bit → ℚ
oneDimPairSum left right =
  bitCharacter left b0 * bitCharacter right b0
  + bitCharacter left b1 * bitCharacter right b1

oneDimCharacterOrthogonality :
  (left right : Bit) →
  oneDimPairSum left right ≡ two * bitDelta left right
oneDimCharacterOrthogonality b0 b0 = solve []
oneDimCharacterOrthogonality b0 b1 = solve []
oneDimCharacterOrthogonality b1 b0 = solve []
oneDimCharacterOrthogonality b1 b1 = solve []

character3 : Bit3 → Bit3 → ℚ
character3 (bit3 k1 k2 k3) (bit3 x1 x2 x3) =
  bitCharacter k1 x1
  * bitCharacter k2 x2
  * bitCharacter k3 x3

modeDelta : Bit3 → Bit3 → ℚ
modeDelta (bit3 k1 k2 k3) (bit3 l1 l2 l3) =
  bitDelta k1 l1 * bitDelta k2 l2 * bitDelta k3 l3

p000 p001 p010 p011 p100 p101 p110 p111 : Bit3
p000 = bit3 b0 b0 b0
p001 = bit3 b0 b0 b1
p010 = bit3 b0 b1 b0
p011 = bit3 b0 b1 b1
p100 = bit3 b1 b0 b0
p101 = bit3 b1 b0 b1
p110 = bit3 b1 b1 b0
p111 = bit3 b1 b1 b1

eightPointPairSum : Bit3 → Bit3 → ℚ
eightPointPairSum left right =
    character3 left p000 * character3 right p000
  + character3 left p001 * character3 right p001
  + character3 left p010 * character3 right p010
  + character3 left p011 * character3 right p011
  + character3 left p100 * character3 right p100
  + character3 left p101 * character3 right p101
  + character3 left p110 * character3 right p110
  + character3 left p111 * character3 right p111

eightPointPairSumFactorizes :
  (k1 k2 k3 l1 l2 l3 : Bit) →
  eightPointPairSum (bit3 k1 k2 k3) (bit3 l1 l2 l3)
  ≡ oneDimPairSum k1 l1
    * oneDimPairSum k2 l2
    * oneDimPairSum k3 l3
eightPointPairSumFactorizes k1 k2 k3 l1 l2 l3 =
  solve
    ( bitCharacter k1 b0 * bitCharacter l1 b0
    ∷ bitCharacter k1 b1 * bitCharacter l1 b1
    ∷ bitCharacter k2 b0 * bitCharacter l2 b0
    ∷ bitCharacter k2 b1 * bitCharacter l2 b1
    ∷ bitCharacter k3 b0 * bitCharacter l3 b0
    ∷ bitCharacter k3 b1 * bitCharacter l3 b1
    ∷ [])

eightPointCharacterOrthogonality :
  (left right : Bit3) →
  eightPointPairSum left right ≡ eight * modeDelta left right
eightPointCharacterOrthogonality
  (bit3 k1 k2 k3) (bit3 l1 l2 l3) =
  begin
    eightPointPairSum (bit3 k1 k2 k3) (bit3 l1 l2 l3)
  ≡⟨ eightPointPairSumFactorizes k1 k2 k3 l1 l2 l3 ⟩
    oneDimPairSum k1 l1
      * oneDimPairSum k2 l2
      * oneDimPairSum k3 l3
  ≡⟨ cong
       (λ first →
         first * oneDimPairSum k2 l2 * oneDimPairSum k3 l3)
       (oneDimCharacterOrthogonality k1 l1) ⟩
    (two * bitDelta k1 l1)
      * oneDimPairSum k2 l2
      * oneDimPairSum k3 l3
  ≡⟨ cong
       (λ second →
         (two * bitDelta k1 l1) * second * oneDimPairSum k3 l3)
       (oneDimCharacterOrthogonality k2 l2) ⟩
    (two * bitDelta k1 l1)
      * (two * bitDelta k2 l2)
      * oneDimPairSum k3 l3
  ≡⟨ cong
       (λ third →
         (two * bitDelta k1 l1)
         * (two * bitDelta k2 l2)
         * third)
       (oneDimCharacterOrthogonality k3 l3) ⟩
    (two * bitDelta k1 l1)
      * (two * bitDelta k2 l2)
      * (two * bitDelta k3 l3)
  ≡⟨ solve
       ( bitDelta k1 l1
       ∷ bitDelta k2 l2
       ∷ bitDelta k3 l3
       ∷ []) ⟩
    eight * modeDelta (bit3 k1 k2 k3) (bit3 l1 l2 l3)
  ∎

selfModeDelta : (mode : Bit3) → modeDelta mode mode ≡ 1ℚ
selfModeDelta (bit3 b0 b0 b0) = refl
selfModeDelta (bit3 b0 b0 b1) = refl
selfModeDelta (bit3 b0 b1 b0) = refl
selfModeDelta (bit3 b0 b1 b1) = refl
selfModeDelta (bit3 b1 b0 b0) = refl
selfModeDelta (bit3 b1 b0 b1) = refl
selfModeDelta (bit3 b1 b1 b0) = refl
selfModeDelta (bit3 b1 b1 b1) = refl

characterSelfMass :
  (mode : Bit3) →
  eightPointPairSum mode mode ≡ eight
characterSelfMass mode =
  trans
    (eightPointCharacterOrthogonality mode mode)
    (trans
      (cong (eight *_) (selfModeDelta mode))
      (solve []))
