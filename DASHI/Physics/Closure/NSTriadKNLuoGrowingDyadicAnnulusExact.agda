module DASHI.Physics.Closure.NSTriadKNLuoGrowingDyadicAnnulusExact where

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
-- Put an actual dyadic annulus predicate on the growing cube carrier. The
-- axis `Fin(4*2^q+1)` is centred at radius `2^(q+1)`. A mode is retained when
-- its infinity-distance from the centre satisfies
--
--   2^(q-1) <= |k|_infinity < 2^(q+1),
--
-- with the q=0 lower endpoint interpreted as zero. Intersecting this annulus
-- with any Boolean Galerkin cutoff still obeys the previously proved bound
--
--   supportCount(q,N) <= 125 * 8^q.
--
-- Thus the support theorem is now attached to an explicit dyadic predicate,
-- not an arbitrary filter alone.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Fin.Base as Fin
open import Data.Product.Base using (proj₁; proj₂)
open import Data.Rational.Base using (_≤_)

import DASHI.Physics.Closure.NSTriadKNLuoGrowingFiniteCubeSupportExact as Growing
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicSupportCountExact as Support
import DASHI.Physics.Closure.NSTriadKNLuoIntegerCubeSupportCapacityExact as Capacity

andBool : Bool → Bool → Bool
andBool true true = true
andBool true false = false
andBool false right = false

natLeBool : Nat → Nat → Bool
natLeBool zero right = true
natLeBool (suc left) zero = false
natLeBool (suc left) (suc right) = natLeBool left right

natLtBool : Nat → Nat → Bool
natLtBool left zero = false
natLtBool zero (suc right) = true
natLtBool (suc left) (suc right) = natLtBool left right

natMaximum : Nat → Nat → Nat
natMaximum zero right = right
natMaximum left zero = left
natMaximum (suc left) (suc right) = suc (natMaximum left right)

absoluteDifference : Nat → Nat → Nat
absoluteDifference zero right = right
absoluteDifference left zero = left
absoluteDifference (suc left) (suc right) = absoluteDifference left right

upperRadius : Nat → Nat
upperRadius shell = Growing.powTwoNat (suc shell)

lowerRadius : Nat → Nat
lowerRadius zero = zero
lowerRadius (suc shell) = Growing.powTwoNat shell

axisDistance :
  (shell : Nat) →
  Growing.AxisAt shell → Nat
axisDistance shell coordinate =
  absoluteDifference (Fin.toℕ coordinate) (upperRadius shell)

firstCoordinate :
  ∀ {shell : Nat} → Growing.ModeAt shell → Growing.AxisAt shell
firstCoordinate mode = proj₁ mode

secondCoordinate :
  ∀ {shell : Nat} → Growing.ModeAt shell → Growing.AxisAt shell
secondCoordinate mode = proj₁ (proj₂ mode)

thirdCoordinate :
  ∀ {shell : Nat} → Growing.ModeAt shell → Growing.AxisAt shell
thirdCoordinate mode = proj₂ (proj₂ mode)

infinityDistance :
  (shell : Nat) →
  Growing.ModeAt shell → Nat
infinityDistance shell mode =
  natMaximum
    (axisDistance shell (firstCoordinate mode))
    (natMaximum
      (axisDistance shell (secondCoordinate mode))
      (axisDistance shell (thirdCoordinate mode)))

dyadicAnnulusPredicate :
  (shell : Nat) →
  Growing.ModeAt shell → Bool
dyadicAnnulusPredicate shell mode =
  andBool
    (natLeBool (lowerRadius shell) (infinityDistance shell mode))
    (natLtBool (infinityDistance shell mode) (upperRadius shell))

annularSupport :
  (shell : Nat) →
  List (Growing.ModeAt shell)
annularSupport shell =
  Growing.filteredGrowingSupport
    shell
    (dyadicAnnulusPredicate shell)

annularSupportCountBound :
  (shell : Nat) →
  Support.countMass (annularSupport shell)
  ≤ Capacity.oneTwentyFive * Capacity.eightPower shell
annularSupportCountBound shell =
  Growing.filteredGrowingSupportCountBound
    shell
    (dyadicAnnulusPredicate shell)

annulusWithGalerkin :
  (shell : Nat) →
  (Growing.ModeAt shell → Bool) →
  Growing.ModeAt shell → Bool
annulusWithGalerkin shell galerkin mode =
  andBool
    (dyadicAnnulusPredicate shell mode)
    (galerkin mode)

annularGalerkinSupport :
  (shell : Nat) →
  (Growing.ModeAt shell → Bool) →
  List (Growing.ModeAt shell)
annularGalerkinSupport shell galerkin =
  Growing.filteredGrowingSupport
    shell
    (annulusWithGalerkin shell galerkin)

annularGalerkinSupportCountBound :
  (shell : Nat) →
  (galerkin : Growing.ModeAt shell → Bool) →
  Support.countMass (annularGalerkinSupport shell galerkin)
  ≤ Capacity.oneTwentyFive * Capacity.eightPower shell
annularGalerkinSupportCountBound shell galerkin =
  Growing.filteredGrowingSupportCountBound
    shell
    (annulusWithGalerkin shell galerkin)
