module DASHI.Physics.Closure.NSTriadKNLuoConcreteDyadicSupportCount125Exact where

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
-- Combine the repository's explicit dyadic-octant enumeration with the
-- concrete five-by-five-by-five base cube. Every Boolean Littlewood--Paley /
-- Galerkin intersection at shell q has mass at most
--
--   125 * 8^q.
--
-- The fully concrete theorem below constructs the base enumeration and its
-- exact mass internally. No baseMassBound remains at that theorem boundary.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicSupportCountExact as Support
import DASHI.Physics.Closure.NSTriadKNLuoConcreteIntegerCube125EnumerationExact as Cube

oneTwentyFive eight : ℚ
oneTwentyFive = Int.+ 125 / 1
eight = Int.+ 8 / 1

zeroBelowOne : 0ℚ ≤ 1ℚ
zeroBelowOne = toWitness {a? = 0ℚ ≤? 1ℚ} _

oneTwentyFiveNonnegative : 0ℚ ≤ oneTwentyFive
oneTwentyFiveNonnegative =
  toWitness {a? = 0ℚ ≤? oneTwentyFive} _

countMassNonnegative :
  ∀ {A : Set} (items : List A) →
  0ℚ ≤ Support.countMass items
countMassNonnegative [] = ℚₚ.≤-refl
countMassNonnegative (_ ∷ items) =
  L2.addNonnegative zeroBelowOne (countMassNonnegative items)

record ConcreteDyadicSupportData (Mode : Set) : Set₁ where
  constructor concrete-dyadic-support-data
  field
    shellPredicate : Mode → Bool
    baseCube : List Mode
    baseMassBound : Support.countMass baseCube ≤ oneTwentyFive

open ConcreteDyadicSupportData public

concreteDyadicSupportCountBound :
  ∀ {Mode : Set}
    (dataSet : ConcreteDyadicSupportData Mode)
    (shell : Nat) →
  Support.countMass
    (Support.dyadicSupport
      (shellPredicate dataSet)
      (baseCube dataSet)
      shell)
  ≤ oneTwentyFive * Geo.pow eight shell
concreteDyadicSupportCountBound dataSet shell =
  let
    filteredBound =
      Support.dyadicSupportCountBound
        (shellPredicate dataSet)
        (baseCube dataSet)
        shell

    powerNN : 0ℚ ≤ Geo.pow eight shell
    powerNN =
      Geo.powNonnegative eight shell
        (toWitness {a? = 0ℚ ≤? eight} _)

    productBound :
      Geo.pow eight shell * Support.countMass (baseCube dataSet)
      ≤ Geo.pow eight shell * oneTwentyFive
    productBound =
      let instance powerNNI = nonNegative powerNN
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (Geo.pow eight shell)
        (baseMassBound dataSet)

    reordered :
      Geo.pow eight shell * oneTwentyFive
      ≡ oneTwentyFive * Geo.pow eight shell
    reordered = ℚₚ.*-comm (Geo.pow eight shell) oneTwentyFive
  in
  ℚₚ.≤-trans
    filteredBound
    (subst
      (λ upper →
        Geo.pow eight shell * Support.countMass (baseCube dataSet)
        ≤ upper)
      reordered
      productBound)

record FullyConcreteDyadicSupportData : Set where
  constructor fully-concrete-dyadic-support-data
  field
    shellPredicate125 : Cube.Cube125 → Bool

open FullyConcreteDyadicSupportData public

cube125MassBound :
  Support.countMass Cube.cube125 ≤ oneTwentyFive
cube125MassBound =
  subst
    (λ mass → mass ≤ oneTwentyFive)
    (sym Cube.cube125Mass)
    ℚₚ.≤-refl

fullyConcreteSupportData :
  FullyConcreteDyadicSupportData →
  ConcreteDyadicSupportData Cube.Cube125
fullyConcreteSupportData dataSet =
  concrete-dyadic-support-data
    (shellPredicate125 dataSet)
    Cube.cube125
    cube125MassBound

fullyConcreteDyadicSupportCountBound :
  (dataSet : FullyConcreteDyadicSupportData) →
  (shell : Nat) →
  Support.countMass
    (Support.dyadicSupport
      (shellPredicate125 dataSet)
      Cube.cube125
      shell)
  ≤ oneTwentyFive * Geo.pow eight shell
fullyConcreteDyadicSupportCountBound dataSet =
  concreteDyadicSupportCountBound
    (fullyConcreteSupportData dataSet)
