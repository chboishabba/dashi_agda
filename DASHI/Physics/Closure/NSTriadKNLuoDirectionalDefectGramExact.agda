module DASHI.Physics.Closure.NSTriadKNLuoDirectionalDefectGramExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- PURPOSE
-- Ground the good/bad coherence split in an exact rational R^3 identity. For
-- two unit directions xi and eta, define
--
--   Theta(xi,eta) = 1 - (xi . eta)^2.
--
-- Lagrange's identity gives
--
--   Theta(xi,eta) = |xi x eta|^2 >= 0,
--
-- while square nonnegativity gives Theta <= 1. Thus the directional defect
-- used by the F3 split is a checked nonnegative quantity in [0,1], not an
-- uninterpreted scalar.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

record Vec3 : Set where
  constructor vec3
  field
    x y z : ℚ

open Vec3 public

dot : Vec3 → Vec3 → ℚ
dot left right =
  x left * x right + y left * y right + z left * z right

normSquared : Vec3 → ℚ
normSquared value = dot value value

cross : Vec3 → Vec3 → Vec3
cross left right =
  vec3
    (y left * z right - z left * y right)
    (z left * x right - x left * z right)
    (x left * y right - y left * x right)

crossNormSquared : Vec3 → Vec3 → ℚ
crossNormSquared left right = normSquared (cross left right)

lagrangeIdentity :
  (left right : Vec3) →
  normSquared left * normSquared right
    - L2.square (dot left right)
  ≡ crossNormSquared left right
lagrangeIdentity left right =
  solve
    ( x left ∷ y left ∷ z left
    ∷ x right ∷ y right ∷ z right ∷ [])

normSquaredNonnegative :
  (value : Vec3) →
  0ℚ ≤ normSquared value
normSquaredNonnegative value =
  L2.addNonnegative
    (L2.addNonnegative
      (L2.squareNonnegative (x value))
      (L2.squareNonnegative (y value)))
    (L2.squareNonnegative (z value))

crossNormSquaredNonnegative :
  (left right : Vec3) →
  0ℚ ≤ crossNormSquared left right
crossNormSquaredNonnegative left right =
  normSquaredNonnegative (cross left right)

gramDefectNonnegative :
  (left right : Vec3) →
  0ℚ ≤ normSquared left * normSquared right
    - L2.square (dot left right)
gramDefectNonnegative left right =
  subst
    (λ value → 0ℚ ≤ value)
    (sym (lagrangeIdentity left right))
    (crossNormSquaredNonnegative left right)

record UnitDirectionPair : Set where
  constructor unit-direction-pair
  field
    left right : Vec3
    leftUnit : normSquared left ≡ 1ℚ
    rightUnit : normSquared right ≡ 1ℚ

open UnitDirectionPair public

directionalDefect : UnitDirectionPair → ℚ
directionalDefect pair =
  1ℚ - L2.square (dot (left pair) (right pair))

directionalDefectEqualsCrossSquare :
  (pair : UnitDirectionPair) →
  directionalDefect pair
  ≡ crossNormSquared (left pair) (right pair)
directionalDefectEqualsCrossSquare pair =
  let
    gram = lagrangeIdentity (left pair) (right pair)

    units :
      normSquared (left pair) * normSquared (right pair)
        - L2.square (dot (left pair) (right pair))
      ≡ 1ℚ - L2.square (dot (left pair) (right pair))
    units
      rewrite leftUnit pair | rightUnit pair =
      solve (dot (left pair) (right pair) ∷ [])
  in
  trans (sym units) gram

directionalDefectNonnegative :
  (pair : UnitDirectionPair) →
  0ℚ ≤ directionalDefect pair
directionalDefectNonnegative pair =
  subst
    (λ value → 0ℚ ≤ value)
    (sym (directionalDefectEqualsCrossSquare pair))
    (crossNormSquaredNonnegative (left pair) (right pair))

directionalDefectAtMostOne :
  (pair : UnitDirectionPair) →
  directionalDefect pair ≤ 1ℚ
directionalDefectAtMostOne pair =
  let
    squareValue = L2.square (dot (left pair) (right pair))
    squareNN = L2.squareNonnegative (dot (left pair) (right pair))

    addSquare :
      (1ℚ - squareValue) + 0ℚ
      ≤ (1ℚ - squareValue) + squareValue
    addSquare =
      ℚₚ.+-monoʳ-≤ (1ℚ - squareValue) squareNN

    leftMeaning : (1ℚ - squareValue) + 0ℚ ≡ 1ℚ - squareValue
    leftMeaning = solve (squareValue ∷ [])

    rightMeaning : (1ℚ - squareValue) + squareValue ≡ 1ℚ
    rightMeaning = solve (squareValue ∷ [])
  in
  subst
    (λ lower → lower ≤ 1ℚ)
    leftMeaning
    (subst
      (λ upper → (1ℚ - squareValue) + 0ℚ ≤ upper)
      rightMeaning
      addSquare)
