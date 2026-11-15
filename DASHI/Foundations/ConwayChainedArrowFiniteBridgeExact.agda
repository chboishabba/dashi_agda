module DASHI.Foundations.ConwayChainedArrowFiniteBridgeExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
import DASHI.Cognition.RecursiveFibreTower as Fibre

-- Rank zero means one Knuth arrow (ordinary exponentiation).
-- Positive successors raise the hyperoperation rank.
-- The zero-height convention is the existing DASHI tetration convention.
up : Nat → Nat → Nat → Nat
up a zero b = Fibre.pow a b
up a (suc rank) zero = 1
up a (suc rank) (suc height) =
  up a rank (up a (suc rank) height)

-- Positive Conway three-term chains: a -> b -> (rank+1).
-- The zero-rank argument is deliberately outside the Conway domain.
three : Nat → Nat → Nat → Nat
three a b zero = 1
three a b (suc rank) = up a rank b

-- Finite functional iteration, shared by the four-term specialisations.
iterate : (Nat → Nat) → Nat → Nat → Nat
iterate f zero seed = seed
iterate f (suc count) seed = f (iterate f count seed)

-- For positive a,b and c, this is Conway's a -> b -> c -> 2:
-- iterate (lambda x -> a -> b -> x) c times, starting at 1.
fourLastTwo : Nat → Nat → Nat → Nat
fourLastTwo a b c = iterate (three a b) c 1

-- The corresponding terminal-3 layer is an iteration of terminal-2.
fourLastThree : Nat → Nat → Nat → Nat
fourLastThree a b c = iterate (fourLastTwo a b) c 1

conwayExponentiation : (a b : Nat) →
  three a b 1 ≡ Fibre.pow a b
conwayExponentiation a b = refl

conwayTetration : (a b : Nat) →
  three a b 2 ≡ Fibre.tetration a b
conwayTetration a zero = refl
conwayTetration a (suc b)
  rewrite conwayTetration a b = refl

twoThreeTwo : three 2 3 2 ≡ 16
twoThreeTwo = refl

twoTwoTwo : three 2 2 2 ≡ 4
twoTwoTwo = refl

threeTwoTwo : three 3 2 2 ≡ 27
threeTwoTwo = refl

-- Wikipedia's small four-term examples:
-- 2 -> 3 -> 2 -> 2 = 2 -> 3 -> 8 (seven Knuth arrows).
twoThreeTwoTwo : fourLastTwo 2 3 2 ≡ three 2 3 8
twoThreeTwoTwo = refl

-- 3 -> 2 -> 2 -> 2 = 3 -> 2 -> 9 (eight Knuth arrows).
threeTwoTwoTwo : fourLastTwo 3 2 2 ≡ three 3 2 9
threeTwoTwoTwo = refl

fourLastTwoStepTwo : (a b : Nat) →
  fourLastTwo a b 2 ≡ three a b (Fibre.pow a b)
fourLastTwoStepTwo a b = refl

fourLastThreeStepTwo : (a b : Nat) →
  fourLastThree a b 2 ≡ fourLastTwo a b (Fibre.pow a b)
fourLastThreeStepTwo a b = refl

-- Repeated factorials are a different operation from chained arrows.
factorial : Nat → Nat
factorial zero = 1
factorial (suc n) = suc n * factorial n

factorialTower : Nat → Nat → Nat
factorialTower seed height = iterate factorial height seed

factorialTowerThreeOne : factorialTower 3 1 ≡ 6
factorialTowerThreeOne = refl

factorialTowerThreeTwo : factorialTower 3 2 ≡ 720
factorialTowerThreeTwo = refl

-- A bridge to primorial digits belongs to representation/valuation,
-- not to the defining semantics of Conway's arrow operator.
