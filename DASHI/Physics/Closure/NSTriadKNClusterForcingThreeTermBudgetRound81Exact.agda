module DASHI.Physics.Closure.NSTriadKNClusterForcingThreeTermBudgetRound81Exact where

------------------------------------------------------------------------
-- ROUND81 / THREE-TERM OFF-BLOCK FORCING BUDGET
--
-- After the exact strain-eigenbasis reduction, each cluster-complement forcing
-- coordinate has only three pieces:
--
--   local vorticity feedback + pressure-Hessian off-block + viscous off-block.
--
-- This module proves the universal sharp-enough three-term square estimate
--
--   (a+b+c)^2 <= 3(a^2+b^2+c^2)
--
-- and sums it over the two coordinates of a 3D line-vs-plane cluster.  Together
-- with the Round81 Sylvester theorem this converts projector turnover into three
-- separately fundable square currencies, without absolute-majorizing the
-- material derivative before the spectral projection.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteRationalOrderCore as Order

square : ℚ → ℚ
square x = x * x

three : ℚ
three = (+ 3) / 1

threeTermSquareBound :
  (a b c : ℚ) →
  square (a + b + c) ≤ three * (square a + square b + square c)
threeTermSquareBound a b c =
  let
    defect : ℚ
    defect = square (a - b) + square (a - c) + square (b - c)

    defectNN : 0ℚ ≤ defect
    defectNN =
      Order.addNonnegative
        (Order.addNonnegative
          (Order.squareNonnegative (a - b))
          (Order.squareNonnegative (a - c)))
        (Order.squareNonnegative (b - c))

    lifted : square (a + b + c) ≤ square (a + b + c) + defect
    lifted =
      subst
        (λ lower → lower ≤ square (a + b + c) + defect)
        (ℚP.+-identityʳ (square (a + b + c)))
        (ℚP.+-mono-≤
          (ℚP.≤-refl {x = square (a + b + c)})
          defectNN)
  in
  subst
    (λ upper → square (a + b + c) ≤ upper)
    (ℚRing.solve-∀ a b c)
    lifted

record TwoCoordinateThreeTermForcing : Set where
  field
    localA pressureA viscousA totalA : ℚ
    localB pressureB viscousB totalB : ℚ

    totalADecomposes : totalA ≡ localA + pressureA + viscousA
    totalBDecomposes : totalB ≡ localB + pressureB + viscousB

open TwoCoordinateThreeTermForcing public

totalSquareEnergy : TwoCoordinateThreeTermForcing → ℚ
totalSquareEnergy datum = square (totalA datum) + square (totalB datum)

localSquareEnergy : TwoCoordinateThreeTermForcing → ℚ
localSquareEnergy datum = square (localA datum) + square (localB datum)

pressureSquareEnergy : TwoCoordinateThreeTermForcing → ℚ
pressureSquareEnergy datum = square (pressureA datum) + square (pressureB datum)

viscousSquareEnergy : TwoCoordinateThreeTermForcing → ℚ
viscousSquareEnergy datum = square (viscousA datum) + square (viscousB datum)

twoCoordinateThreeTermForcingBound :
  (datum : TwoCoordinateThreeTermForcing) →
  totalSquareEnergy datum
  ≤ three *
    (localSquareEnergy datum
      + pressureSquareEnergy datum
      + viscousSquareEnergy datum)
twoCoordinateThreeTermForcingBound datum =
  let
    first :
      square (totalA datum)
      ≤ three * (square (localA datum)
        + square (pressureA datum) + square (viscousA datum))
    first = subst
      (λ total →
        square total
        ≤ three * (square (localA datum)
          + square (pressureA datum) + square (viscousA datum)))
      (sym (totalADecomposes datum))
      (threeTermSquareBound
        (localA datum) (pressureA datum) (viscousA datum))

    second :
      square (totalB datum)
      ≤ three * (square (localB datum)
        + square (pressureB datum) + square (viscousB datum))
    second = subst
      (λ total →
        square total
        ≤ three * (square (localB datum)
          + square (pressureB datum) + square (viscousB datum)))
      (sym (totalBDecomposes datum))
      (threeTermSquareBound
        (localB datum) (pressureB datum) (viscousB datum))

    summed = ℚP.+-mono-≤ first second
  in
  subst
    (λ upper → totalSquareEnergy datum ≤ upper)
    (ℚRing.solve-∀
      three
      (localA datum) (localB datum)
      (pressureA datum) (pressureB datum)
      (viscousA datum) (viscousB datum))
    summed

round81ThreeTermClusterForcingBudgetConstructed : Bool
round81ThreeTermClusterForcingBudgetConstructed = true

round81ThreeTermClusterForcingBudgetConstructedIsTrue :
  round81ThreeTermClusterForcingBudgetConstructed ≡ true
round81ThreeTermClusterForcingBudgetConstructedIsTrue = refl
