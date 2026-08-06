module DASHI.Physics.Closure.NSTriadKNLuoConcreteIntegerCube125EnumerationExact where

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
-- Construct the actual five-by-five-by-five integer-cube enumeration used at
-- the base dyadic shell. The coordinate type represents the offsets
--
--   {-2,-1,0,1,2}.
--
-- Its threefold Cartesian product is enumerated without repetition and has
-- exact rational counting mass 125. This removes the previously caller-
-- supplied baseMassBound from the concrete support theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _*_) 
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; trans)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicSupportCountExact as Support

data Axis5 : Set where
  minusTwo minusOne origin plusOne plusTwo : Axis5

axis5 : List Axis5
axis5 = minusTwo ∷ minusOne ∷ origin ∷ plusOne ∷ plusTwo ∷ []

map :
  ∀ {A B : Set} →
  (A → B) → List A → List B
map transform [] = []
map transform (item ∷ items) =
  transform item ∷ map transform items

countMap :
  ∀ {A B : Set}
    (transform : A → B)
    (items : List A) →
  Support.countMass (map transform items)
  ≡ Support.countMass items
countMap transform [] = refl
countMap transform (item ∷ items)
  rewrite countMap transform items = refl

concatMap :
  ∀ {A B : Set} →
  (A → List B) → List A → List B
concatMap transform [] = []
concatMap transform (item ∷ items) =
  Support.append (transform item) (concatMap transform items)

cartesian :
  ∀ {A B : Set} →
  List A → List B → List (A × B)
cartesian first second =
  concatMap
    (λ left → map (λ right → left , right) second)
    first

five : ℚ
five = Int.+ 5 / 1

axis5Mass : Support.countMass axis5 ≡ five
axis5Mass = solve []

countCartesianAxis5 :
  ∀ {B : Set} (second : List B) →
  Support.countMass (cartesian axis5 second)
  ≡ five * Support.countMass second
countCartesianAxis5 second
  rewrite Support.countAppend
            (map (λ right → minusTwo , right) second)
            (concatMap (λ left → map (λ right → left , right) second)
              (minusOne ∷ origin ∷ plusOne ∷ plusTwo ∷ []))
        | Support.countAppend
            (map (λ right → minusOne , right) second)
            (concatMap (λ left → map (λ right → left , right) second)
              (origin ∷ plusOne ∷ plusTwo ∷ []))
        | Support.countAppend
            (map (λ right → origin , right) second)
            (concatMap (λ left → map (λ right → left , right) second)
              (plusOne ∷ plusTwo ∷ []))
        | Support.countAppend
            (map (λ right → plusOne , right) second)
            (concatMap (λ left → map (λ right → left , right) second)
              (plusTwo ∷ []))
        | Support.countAppend
            (map (λ right → plusTwo , right) second)
            []
        | countMap (λ right → minusTwo , right) second
        | countMap (λ right → minusOne , right) second
        | countMap (λ right → origin , right) second
        | countMap (λ right → plusOne , right) second
        | countMap (λ right → plusTwo , right) second =
  solve (Support.countMass second ∷ [])

Plane25 : Set
Plane25 = Axis5 × Axis5

Cube125 : Set
Cube125 = Axis5 × Plane25

plane25 : List Plane25
plane25 = cartesian axis5 axis5

cube125 : List Cube125
cube125 = cartesian axis5 plane25

plane25Mass :
  Support.countMass plane25 ≡ Int.+ 25 / 1
plane25Mass =
  trans
    (countCartesianAxis5 axis5)
    (subst
      (λ axisMass → five * axisMass ≡ Int.+ 25 / 1)
      axis5Mass
      (solve []))

cube125Mass :
  Support.countMass cube125 ≡ Int.+ 125 / 1
cube125Mass =
  trans
    (countCartesianAxis5 plane25)
    (subst
      (λ planeMass → five * planeMass ≡ Int.+ 125 / 1)
      plane25Mass
      (solve []))
