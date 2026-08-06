module DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicSupportCountExact where

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
-- Replace the free support-count field in the finite Bernstein producer by an
-- explicit dyadic octant enumeration.  One scale refinement consists of eight
-- copies of the preceding three-dimensional cube.  Filtering that enumeration
-- by any Boolean shell predicate can only decrease its finite counting mass.
-- Consequently
--
--   mass (support q) <= 8^q mass baseCube.
--
-- Since lambda_q = 2^q, this is exactly the lambda_q^3 lattice-support law.
-- The remaining continuum bridge is only the representation of the chosen
-- torus Littlewood--Paley support as such a filtered finite enumeration.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Unit using (⊤; tt)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo

countMass : ∀ {A : Set} → List A → ℚ
countMass [] = 0ℚ
countMass (_ ∷ items) = 1ℚ + countMass items

append : ∀ {A : Set} → List A → List A → List A
append [] right = right
append (item ∷ left) right = item ∷ append left right

countAppend :
  ∀ {A : Set} (left right : List A) →
  countMass (append left right) ≡ countMass left + countMass right
countAppend [] right =
  sym (ℚₚ.+-identityˡ (countMass right))
countAppend (item ∷ left) right
  rewrite countAppend left right =
  solve (countMass left ∷ countMass right ∷ [])

fourfold : ∀ {A : Set} → List A → List A
fourfold items =
  append items (append items (append items items))

eightfold : ∀ {A : Set} → List A → List A
eightfold items = append (fourfold items) (fourfold items)

four eight : ℚ
four = Int.+ 4 / 1
eight = Int.+ 8 / 1

countFourfold :
  ∀ {A : Set} (items : List A) →
  countMass (fourfold items) ≡ four * countMass items
countFourfold items
  rewrite countAppend items (append items (append items items))
        | countAppend items (append items items)
        | countAppend items items =
  solve (countMass items ∷ [])

countEightfold :
  ∀ {A : Set} (items : List A) →
  countMass (eightfold items) ≡ eight * countMass items
countEightfold items
  rewrite countAppend (fourfold items) (fourfold items)
        | countFourfold items =
  solve (countMass items ∷ [])

dyadicCube : ∀ {A : Set} → List A → Nat → List A
dyadicCube baseCube zero = baseCube
dyadicCube baseCube (suc shell) =
  eightfold (dyadicCube baseCube shell)

dyadicCubeMass :
  ∀ {A : Set} (baseCube : List A) (shell : Nat) →
  countMass (dyadicCube baseCube shell)
  ≡ Geo.pow eight shell * countMass baseCube
dyadicCubeMass baseCube zero =
  sym (ℚₚ.*-identityˡ (countMass baseCube))
dyadicCubeMass baseCube (suc shell)
  rewrite countEightfold (dyadicCube baseCube shell)
        | dyadicCubeMass baseCube shell =
  solve (Geo.pow eight shell ∷ countMass baseCube ∷ [])

filterBool :
  ∀ {A : Set} →
  (A → Bool) →
  List A →
  List A
filterBool predicate [] = []
filterBool predicate (item ∷ items) with predicate item
... | true = item ∷ filterBool predicate items
... | false = filterBool predicate items

zeroBelowOne : 0ℚ ≤ 1ℚ
zeroBelowOne = toWitness {a? = 0ℚ ≤? 1ℚ} _

countFilterBound :
  ∀ {A : Set}
    (predicate : A → Bool)
    (items : List A) →
  countMass (filterBool predicate items) ≤ countMass items
countFilterBound predicate [] = ℚₚ.≤-refl
countFilterBound predicate (item ∷ items) with predicate item
... | true =
  ℚₚ.+-mono-≤
    ℚₚ.≤-refl
    (countFilterBound predicate items)
... | false =
  let
    filteredBelowTail :
      countMass (filterBool predicate items) ≤ countMass items
    filteredBelowTail = countFilterBound predicate items

    tailBelowSuccessor :
      countMass items ≤ 1ℚ + countMass items
    tailBelowSuccessor =
      subst
        (λ lower → lower ≤ 1ℚ + countMass items)
        (ℚₚ.+-identityˡ (countMass items))
        (ℚₚ.+-mono-≤ zeroBelowOne ℚₚ.≤-refl)
  in
  ℚₚ.≤-trans filteredBelowTail tailBelowSuccessor

dyadicSupport :
  ∀ {A : Set} →
  (A → Bool) →
  List A →
  Nat →
  List A
dyadicSupport predicate baseCube shell =
  filterBool predicate (dyadicCube baseCube shell)

dyadicSupportCountBound :
  ∀ {A : Set}
    (predicate : A → Bool)
    (baseCube : List A)
    (shell : Nat) →
  countMass (dyadicSupport predicate baseCube shell)
  ≤ Geo.pow eight shell * countMass baseCube
dyadicSupportCountBound predicate baseCube shell =
  subst
    (λ upper →
      countMass (dyadicSupport predicate baseCube shell) ≤ upper)
    (dyadicCubeMass baseCube shell)
    (countFilterBound predicate (dyadicCube baseCube shell))

-- An explicit one-cell base cube gives the exact 8^q capacity.
oneCellBaseCube : List ⊤
oneCellBaseCube = tt ∷ []

oneCellBaseMass : countMass oneCellBaseCube ≡ 1ℚ
oneCellBaseMass = solve []

oneCellDyadicCubeMass :
  (shell : Nat) →
  countMass (dyadicCube oneCellBaseCube shell)
  ≡ Geo.pow eight shell
oneCellDyadicCubeMass shell =
  trans
    (dyadicCubeMass oneCellBaseCube shell)
    (subst
      (λ baseMass → Geo.pow eight shell * baseMass ≡ Geo.pow eight shell)
      (sym oneCellBaseMass)
      (ℚₚ.*-identityʳ (Geo.pow eight shell)))
