module DASHI.Mathematics.Symmetry.TetragonalD4hNormalFormExact where

-- Classical D4 x C2 presented by (rotation exponent, reflection bit,
-- horizontal mirror bit). The eight equatorial/height sites provide a
-- concrete action. This file contains proof terms, not a claimed
-- machine-checked result until the Agda compiler has accepted them.
--
-- Reuses the finite permutation carrier in
-- TetragonalD4hGeneratorActionExact; no experimental crystal identified.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Mathematics.Symmetry.TetragonalD4hGeneratorActionExact as Geo

data Quarter : Set where
  q0 q1 q2 q3 : Quarter

next : Quarter → Quarter
next q0 = q1
next q1 = q2
next q2 = q3
next q3 = q0

add : Quarter → Quarter → Quarter
add q0 b = b
add q1 b = next b
add q2 b = next (next b)
add q3 b = next (next (next b))

neg : Quarter → Quarter
neg q0 = q0
neg q1 = q3
neg q2 = q2
neg q3 = q1

xor : Bool → Bool → Bool
xor false b = b
xor true false = true
xor true true = false

signed : Bool → Quarter → Quarter
signed false q = q
signed true q = neg q

record D4h : Set where
  constructor element
  field
    rotation : Quarter
    vertical : Bool
    horizontal : Bool
open D4h public

identity : D4h
identity = element q0 false false

compose : D4h → D4h → D4h
compose (element a b c) (element d e f) =
  element (add a (signed b d)) (xor b e) (xor c f)

quarterAct : Quarter → Geo.Site → Geo.Site
quarterAct q0 p = p
quarterAct q1 p = Geo.R p
quarterAct q2 p = Geo.R (Geo.R p)
quarterAct q3 p = Geo.R (Geo.R (Geo.R p))

verticalAct : Bool → Geo.Site → Geo.Site
verticalAct false p = p
verticalAct true p = Geo.S p

horizontalAct : Bool → Geo.Site → Geo.Site
horizontalAct false p = p
horizontalAct true p = Geo.H p

act : D4h → Geo.Site → Geo.Site
act (element a b c) p =
  quarterAct a (verticalAct b (horizontalAct c p))

-- The following 16 element descriptions are distinct by construction,
-- because D4h is a record of finite component types. To establish the
-- group and action laws in the kernel, add proofs for add-associativity,
-- signed-add distributivity, and composeActs; those obligations are not
-- smuggled in as postulates.
elements : D4h → D4h
elements g = g

-- A small set of definitional witnesses for the faithful permutation action.
rotationMovesNorth :
  act (element q1 false false) (Geo.site Geo.north Geo.above)
  ≡ Geo.site Geo.east Geo.above
rotationMovesNorth = refl

verticalReflectsEast :
  act (element q0 true false) (Geo.site Geo.east Geo.above)
  ≡ Geo.site Geo.west Geo.above
verticalReflectsEast = refl

horizontalFlipsHeight :
  act (element q0 false true) (Geo.site Geo.north Geo.above)
  ≡ Geo.site Geo.north Geo.below
horizontalFlipsHeight = refl

-- Complete identity, associativity, inverses and action composition can be
-- proved by finite computation over these 4×2×2 constructors. The following
-- lemmas provide the identity and the literal inverse on the normal form.

inverse : D4h → D4h
inverse (element a false c) = element (neg a) false c
inverse (element a true c) = element a true c

identityLeft : (g : D4h) → compose identity g ≡ g
identityLeft (element q0 false false) = refl
identityLeft (element q0 false true) = refl
identityLeft (element q0 true false) = refl
identityLeft (element q0 true true) = refl
identityLeft (element q1 false false) = refl
identityLeft (element q1 false true) = refl
identityLeft (element q1 true false) = refl
identityLeft (element q1 true true) = refl
identityLeft (element q2 false false) = refl
identityLeft (element q2 false true) = refl
identityLeft (element q2 true false) = refl
identityLeft (element q2 true true) = refl
identityLeft (element q3 false false) = refl
identityLeft (element q3 false true) = refl
identityLeft (element q3 true false) = refl
identityLeft (element q3 true true) = refl

identityRight : (g : D4h) → compose g identity ≡ g
identityRight (element q0 false false) = refl
identityRight (element q0 false true) = refl
identityRight (element q0 true false) = refl
identityRight (element q0 true true) = refl
identityRight (element q1 false false) = refl
identityRight (element q1 false true) = refl
identityRight (element q1 true false) = refl
identityRight (element q1 true true) = refl
identityRight (element q2 false false) = refl
identityRight (element q2 false true) = refl
identityRight (element q2 true false) = refl
identityRight (element q2 true true) = refl
identityRight (element q3 false false) = refl
identityRight (element q3 false true) = refl
identityRight (element q3 true false) = refl
identityRight (element q3 true true) = refl

inverseLeft : (g : D4h) → compose (inverse g) g ≡ identity
inverseLeft (element q0 false false) = refl
inverseLeft (element q0 false true) = refl
inverseLeft (element q0 true false) = refl
inverseLeft (element q0 true true) = refl
inverseLeft (element q1 false false) = refl
inverseLeft (element q1 false true) = refl
inverseLeft (element q1 true false) = refl
inverseLeft (element q1 true true) = refl
inverseLeft (element q2 false false) = refl
inverseLeft (element q2 false true) = refl
inverseLeft (element q2 true false) = refl
inverseLeft (element q2 true true) = refl
inverseLeft (element q3 false false) = refl
inverseLeft (element q3 false true) = refl
inverseLeft (element q3 true false) = refl
inverseLeft (element q3 true true) = refl

inverseRight : (g : D4h) → compose g (inverse g) ≡ identity
inverseRight (element q0 false false) = refl
inverseRight (element q0 false true) = refl
inverseRight (element q0 true false) = refl
inverseRight (element q0 true true) = refl
inverseRight (element q1 false false) = refl
inverseRight (element q1 false true) = refl
inverseRight (element q1 true false) = refl
inverseRight (element q1 true true) = refl
inverseRight (element q2 false false) = refl
inverseRight (element q2 false true) = refl
inverseRight (element q2 true false) = refl
inverseRight (element q2 true true) = refl
inverseRight (element q3 false false) = refl
inverseRight (element q3 false true) = refl
inverseRight (element q3 true false) = refl
inverseRight (element q3 true true) = refl
