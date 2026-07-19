module DASHI.Core.TriadicClosureTower where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import DASHI.Algebra.Trit using (Trit)

------------------------------------------------------------------------
-- Finite cardinal arithmetic
--
-- tower b h uses h stacked copies of b:
--   tower b 0 = 1
--   tower b 1 = b
--   tower b 2 = b ^ b
--   tower b 3 = b ^ (b ^ b)
------------------------------------------------------------------------

pow : Nat → Nat → Nat
pow b zero = 1
pow b (suc n) = b * pow b n

tower : Nat → Nat → Nat
tower b zero = 1
tower b (suc h) = pow b (tower b h)

threeTowerOne : tower 3 1 ≡ 3
threeTowerOne = refl

threeTowerTwo : tower 3 2 ≡ 27
threeTowerTwo = refl

nineTowerOne : tower 9 1 ≡ 9
nineTowerOne = refl

------------------------------------------------------------------------
-- The first nonary carrier
------------------------------------------------------------------------

data Nonary : Set where
  n0 n1 n2 n3 n4 n5 n6 n7 n8 : Nonary

------------------------------------------------------------------------
-- Cartesian products and genuine power towers are different constructions.
--
-- A three-axis Cartesian carrier has 3 * 3 * 3 = 27 states.
-- A function-space tower instead satisfies c₀ = 3 and cₙ₊₁ = 3 ^ cₙ.
------------------------------------------------------------------------

ThreeAxis : Set → Set
ThreeAxis A = Trit → A

TriadicCube : Set
TriadicCube = ThreeAxis Trit

ThreeTowerCarrier : Nat → Set
ThreeTowerCarrier zero = Trit
ThreeTowerCarrier (suc depth) = ThreeTowerCarrier depth → Trit

NineTowerCarrier : Nat → Set
NineTowerCarrier zero = Nonary
NineTowerCarrier (suc depth) = NineTowerCarrier depth → Nonary

-- The zero index names the bottom carrier itself.  Therefore:
--   ThreeTowerCarrier 0 has cardinality 3,
--   ThreeTowerCarrier 1 has cardinality 3 ^ 3 = 27,
--   ThreeTowerCarrier 2 has cardinality 3 ^ (3 ^ 3).
-- Likewise NineTowerCarrier 7 denotes a tower with eight stacked 9s.

ThreeSuperThree : Set
ThreeSuperThree = ThreeTowerCarrier 1

ThreeSuperThreeSuperThree : Set
ThreeSuperThreeSuperThree = ThreeTowerCarrier 2

NineClosureHeightEight : Set
NineClosureHeightEight = NineTowerCarrier 7

------------------------------------------------------------------------
-- M3 / M6 / M9 role separation
--
-- M3 is an object/stance.
-- M6 is an unsublated arrow holding two objects in opposition.
-- M9 is a closure object carrying that arrow together with its synthesis.
------------------------------------------------------------------------

M3 : Set → Set
M3 A = A

record M6Arrow (A : Set) : Set where
  constructor tension
  field
    source : A
    target : A

open M6Arrow public

record M9Closure (A : Set) : Set where
  constructor close
  field
    opposition : M6Arrow A
    synthesis  : A

open M9Closure public

sublate : {A : Set} → M9Closure A → A
sublate closure = synthesis closure

-- A 6-of-9 is an unsublated opposition between two already closed worlds.
SixOfNine : Set → Set
SixOfNine A = M6Arrow (M9Closure A)

-- A 9-of-9 applies closure again at the level of closed worlds.
NineOfNine : Set → Set
NineOfNine A = M9Closure (M9Closure A)

-- A minimum triadic axis of closed worlds: three positions, each carrying an M9.
ThreeOfNine : Set → Set
ThreeOfNine A = ThreeAxis (M9Closure A)

-- The closure ladder may be iterated without identifying the arrow with its
-- closure.  M6 is traversed by supplying an M9 synthesis at the same level.
promoteSix : {A : Set} → M6Arrow A → A → M9Closure A
promoteSix arrow result = close arrow result

promoteSixOfNine : {A : Set} → SixOfNine A → M9Closure A → NineOfNine A
promoteSixOfNine arrow result = close arrow result
