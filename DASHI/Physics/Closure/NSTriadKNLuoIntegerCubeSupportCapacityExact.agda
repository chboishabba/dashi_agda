module DASHI.Physics.Closure.NSTriadKNLuoIntegerCubeSupportCapacityExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Loukas Grafakos.
-- Title: "Classical Fourier Analysis".
-- DOI: 10.1007/978-1-4939-1194-3.
--
-- PURPOSE
-- Prove the numerical core of the actual Z^3 dyadic support count.  The
-- annulus
--
--   2^(q-1) <= |k|_infinity < 2^(q+1)
--
-- lies in the integer cube with coordinate capacity
--
--   2 * 2^(q+1) + 1 = 4 * 2^q + 1.
--
-- Since 1 <= 2^q,
--
--   (4 * 2^q + 1)^3 <= (5 * 2^q)^3 = 125 * 8^q.
--
-- This module proves that complete exact rational arithmetic.  A concrete
-- enumeration/filter module only has to identify its retained support count
-- with a quantity below this cube capacity.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

two four five eight oneTwentyFive : ℚ
two = Int.+ 2 / 1
four = Int.+ 4 / 1
five = Int.+ 5 / 1
eight = Int.+ 8 / 1
oneTwentyFive = Int.+ 125 / 1

zeroBelowOne : 0ℚ ≤ 1ℚ
zeroBelowOne = toWitness {a? = 0ℚ ≤? 1ℚ} _

oneBelowTwo : 1ℚ ≤ two
oneBelowTwo = toWitness {a? = 1ℚ ≤? two} _

twoNonnegative : 0ℚ ≤ two
twoNonnegative = toWitness {a? = 0ℚ ≤? two} _

fourNonnegative : 0ℚ ≤ four
fourNonnegative = toWitness {a? = 0ℚ ≤? four} _

fiveNonnegative : 0ℚ ≤ five
fiveNonnegative = toWitness {a? = 0ℚ ≤? five} _

eightNonnegative : 0ℚ ≤ eight
eightNonnegative = toWitness {a? = 0ℚ ≤? eight} _

oneTwentyFiveNonnegative : 0ℚ ≤ oneTwentyFive
oneTwentyFiveNonnegative =
  toWitness {a? = 0ℚ ≤? oneTwentyFive} _

twoPower : Nat → ℚ
twoPower = Geo.pow two

eightPower : Nat → ℚ
eightPower = Geo.pow eight

cube : ℚ → ℚ
cube value = value * value * value

oneBelowTwoPower :
  (shell : Nat) → 1ℚ ≤ twoPower shell
oneBelowTwoPower zero = ℚₚ.≤-refl
oneBelowTwoPower (suc shell) =
  let
    productBound :
      1ℚ * 1ℚ ≤ two * twoPower shell
    productBound =
      L2.nonnegativeProductMonotone
        zeroBelowOne zeroBelowOne
        twoNonnegative
        (Geo.powNonnegative two shell twoNonnegative)
        oneBelowTwo
        (oneBelowTwoPower shell)

    leftMeaning : 1ℚ * 1ℚ ≡ 1ℚ
    leftMeaning = solve []
  in
  subst
    (λ lower → lower ≤ two * twoPower shell)
    leftMeaning
    productBound

cubeSide : Nat → ℚ
cubeSide shell = four * twoPower shell + 1ℚ

cubeCapacity : Nat → ℚ
cubeCapacity shell = cube (cubeSide shell)

cubeSideNonnegative :
  (shell : Nat) → 0ℚ ≤ cubeSide shell
cubeSideNonnegative shell =
  L2.addNonnegative
    (let
       instance
         fourNN = nonNegative fourNonnegative
         powerNN =
           nonNegative (Geo.powNonnegative two shell twoNonnegative)
         productNN =
           ℚₚ.nonNeg*nonNeg⇒nonNeg four (twoPower shell)
     in
     ℚₚ.nonNegative⁻¹ (four * twoPower shell))
    zeroBelowOne

fiveTimesPowerNonnegative :
  (shell : Nat) → 0ℚ ≤ five * twoPower shell
fiveTimesPowerNonnegative shell =
  let
    instance
      fiveNN = nonNegative fiveNonnegative
      powerNN = nonNegative (Geo.powNonnegative two shell twoNonnegative)
      productNN = ℚₚ.nonNeg*nonNeg⇒nonNeg five (twoPower shell)
  in
  ℚₚ.nonNegative⁻¹ (five * twoPower shell)

cubeSideBelowFiveTimesPower :
  (shell : Nat) →
  cubeSide shell ≤ five * twoPower shell
cubeSideBelowFiveTimesPower shell =
  let
    addPower :
      four * twoPower shell + 1ℚ
      ≤ four * twoPower shell + twoPower shell
    addPower =
      ℚₚ.+-mono-≤ ℚₚ.≤-refl (oneBelowTwoPower shell)

    endpoint :
      four * twoPower shell + twoPower shell
      ≡ five * twoPower shell
    endpoint = solve (twoPower shell ∷ [])
  in
  subst
    (λ upper → cubeSide shell ≤ upper)
    endpoint
    addPower

cubeMonotoneNonnegative :
  (left right : ℚ) →
  0ℚ ≤ left → 0ℚ ≤ right →
  left ≤ right →
  cube left ≤ cube right
cubeMonotoneNonnegative left right leftNN rightNN left≤right =
  let
    squareBound : left * left ≤ right * right
    squareBound =
      L2.nonnegativeProductMonotone
        leftNN leftNN rightNN rightNN left≤right left≤right

    leftSquareNN = L2.squareNonnegative left
    rightSquareNN = L2.squareNonnegative right
  in
  L2.nonnegativeProductMonotone
    leftSquareNN leftNN rightSquareNN rightNN squareBound left≤right

twoPowerCubeIsEightPower :
  (shell : Nat) →
  cube (twoPower shell) ≡ eightPower shell
twoPowerCubeIsEightPower zero = solve []
twoPowerCubeIsEightPower (suc shell)
  rewrite twoPowerCubeIsEightPower shell =
  solve (twoPower shell ∷ eightPower shell ∷ [])

integerCubeCapacityBound :
  (shell : Nat) →
  cubeCapacity shell ≤ oneTwentyFive * eightPower shell
integerCubeCapacityBound shell =
  let
    sideBound = cubeSideBelowFiveTimesPower shell

    cubeBound :
      cube (cubeSide shell)
      ≤ cube (five * twoPower shell)
    cubeBound =
      cubeMonotoneNonnegative
        (cubeSide shell)
        (five * twoPower shell)
        (cubeSideNonnegative shell)
        (fiveTimesPowerNonnegative shell)
        sideBound

    endpoint :
      cube (five * twoPower shell)
      ≡ oneTwentyFive * eightPower shell
    endpoint =
      subst
        (λ powerCube →
          cube (five * twoPower shell)
          ≡ oneTwentyFive * powerCube)
        (twoPowerCubeIsEightPower shell)
        (solve (twoPower shell ∷ []))
  in
  subst
    (λ upper → cubeCapacity shell ≤ upper)
    endpoint
    cubeBound
