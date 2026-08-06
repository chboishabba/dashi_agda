module DASHI.Physics.Closure.NSTriadKNLuoGrowingFiniteCubeSupportExact where

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
-- Replace the repeated-slot capacity model by an actual growing finite cube.
-- At shell q let
--
--   R_q    = 2^(q+1),
--   side_q = 2 R_q + 1 = 4 * 2^q + 1,
--   Cube_q = Fin(side_q)^3.
--
-- Every coordinate and every three-dimensional mode is explicitly enumerated.
-- The complete cube has exact counting mass side_q^3, and any Boolean annulus
-- / Galerkin intersection has mass at most
--
--   side_q^3 <= 125 * 8^q.
--
-- This closes the finite growing-carrier support count without a base-list or
-- base-mass producer. Interpreting Fin(side_q) as the signed integer interval
-- [-R_q,R_q] is a separate coordinate-label isomorphism, not a cardinality
-- assumption.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Fin.Base as Fin
open Fin using (Fin)
open import Data.Nat.Base using (_+_)
open import Data.Product.Base using (_×_; _,_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicSupportCountExact as Support
import DASHI.Physics.Closure.NSTriadKNLuoFiniteFinEnumerationExact as Finite
import DASHI.Physics.Closure.NSTriadKNLuoConcreteIntegerCube125EnumerationExact as Product
import DASHI.Physics.Closure.NSTriadKNLuoIntegerCubeSupportCapacityExact as Capacity

natMass : Nat → ℚ
natMass zero = 0ℚ
natMass (suc value) = 1ℚ + natMass value

natMassAdd :
  (left right : Nat) →
  natMass (left + right) ≡ natMass left + natMass right
natMassAdd zero right = sym (ℚₚ.+-identityˡ (natMass right))
natMassAdd (suc left) right
  rewrite natMassAdd left right =
  solve (natMass left ∷ natMass right ∷ [])

countEnumerateFin :
  (size : Nat) →
  Support.countMass (Finite.enumerateFin size) ≡ natMass size
countEnumerateFin zero = refl
countEnumerateFin (suc size)
  rewrite Product.countMap Fin.suc (Finite.enumerateFin size)
        | countEnumerateFin size =
  refl

countCartesian :
  ∀ {A B : Set}
    (first : List A)
    (second : List B) →
  Support.countMass (Product.cartesian first second)
  ≡ Support.countMass first * Support.countMass second
countCartesian [] second = solve []
countCartesian (item ∷ items) second
  rewrite Support.countAppend
            (Product.map (λ right → item , right) second)
            (Product.cartesian items second)
        | Product.countMap (λ right → item , right) second
        | countCartesian items second =
  solve
    (Support.countMass items ∷ Support.countMass second ∷ [])

powTwoNat : Nat → Nat
powTwoNat zero = suc zero
powTwoNat (suc exponent) =
  powTwoNat exponent + powTwoNat exponent

two : ℚ
two = Int.+ 2 / 1

natMassPowTwo :
  (exponent : Nat) →
  natMass (powTwoNat exponent) ≡ Geo.pow two exponent
natMassPowTwo zero = solve []
natMassPowTwo (suc exponent)
  rewrite natMassAdd (powTwoNat exponent) (powTwoNat exponent)
        | natMassPowTwo exponent =
  solve (Geo.pow two exponent ∷ [])

quadruple : Nat → Nat
quadruple value = value + value + value + value

sideNat : Nat → Nat
sideNat shell = suc (quadruple (powTwoNat shell))

natMassQuadruple :
  (value : Nat) →
  natMass (quadruple value) ≡
  Capacity.four * natMass value
natMassQuadruple value
  rewrite natMassAdd (value + value + value) value
        | natMassAdd (value + value) value
        | natMassAdd value value =
  solve (natMass value ∷ [])

natMassSide :
  (shell : Nat) →
  natMass (sideNat shell) ≡ Capacity.cubeSide shell
natMassSide shell =
  trans
    (cong (1ℚ +_)
      (trans
        (natMassQuadruple (powTwoNat shell))
        (cong (Capacity.four *_)
          (natMassPowTwo shell))))
    (solve (Capacity.twoPower shell ∷ []))

AxisAt : Nat → Set
AxisAt shell = Fin (sideNat shell)

ModeAt : Nat → Set
ModeAt shell = AxisAt shell × (AxisAt shell × AxisAt shell)

axisModes : (shell : Nat) → List (AxisAt shell)
axisModes shell = Finite.enumerateFin (sideNat shell)

modeCube : (shell : Nat) → List (ModeAt shell)
modeCube shell =
  Product.cartesian
    (axisModes shell)
    (Product.cartesian (axisModes shell) (axisModes shell))

axisModesMass :
  (shell : Nat) →
  Support.countMass (axisModes shell) ≡ Capacity.cubeSide shell
axisModesMass shell =
  trans
    (countEnumerateFin (sideNat shell))
    (natMassSide shell)

modeCubeMass :
  (shell : Nat) →
  Support.countMass (modeCube shell) ≡ Capacity.cubeCapacity shell
modeCubeMass shell =
  trans
    (trans
      (countCartesian
        (axisModes shell)
        (Product.cartesian (axisModes shell) (axisModes shell)))
      (cong
        (Support.countMass (axisModes shell) *_)
        (countCartesian (axisModes shell) (axisModes shell))))
    (subst
      (λ sideMass →
        sideMass * (sideMass * sideMass)
        ≡ Capacity.cubeCapacity shell)
      (sym (axisModesMass shell))
      (solve (Capacity.cubeSide shell ∷ [])))

filteredGrowingSupport :
  (shell : Nat) →
  (ModeAt shell → Bool) →
  List (ModeAt shell)
filteredGrowingSupport shell predicate =
  Support.filterBool predicate (modeCube shell)

filteredGrowingSupportCountBound :
  (shell : Nat) →
  (predicate : ModeAt shell → Bool) →
  Support.countMass (filteredGrowingSupport shell predicate)
  ≤ Capacity.oneTwentyFive * Capacity.eightPower shell
filteredGrowingSupportCountBound shell predicate =
  ℚₚ.≤-trans
    (Support.countFilterBound predicate (modeCube shell))
    (subst
      (λ lower →
        lower ≤ Capacity.oneTwentyFive * Capacity.eightPower shell)
      (sym (modeCubeMass shell))
      (Capacity.integerCubeCapacityBound shell))
