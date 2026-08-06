module DASHI.Physics.Closure.NSTriadKNLuoPeriodicGalerkinSupportUniformExact where

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
-- Add the actual logical structure of a Galerkin shell support.  A retained
-- mode must pass both the Littlewood--Paley annulus predicate and an arbitrary
-- finite Galerkin cutoff predicate.  Intersecting with the cutoff cannot
-- enlarge the shell, so the existing 8^q three-dimensional support capacity
-- is uniform in the truncation parameter.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _*_; _≤_)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicSupportCountExact as Support
import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo

andBool : Bool → Bool → Bool
andBool true true = true
andBool true false = false
andBool false right = false

combinedPredicate :
  ∀ {Mode : Set} →
  (Mode → Bool) →
  (Mode → Bool) →
  Mode → Bool
combinedPredicate littlewoodPaley galerkin mode =
  andBool (littlewoodPaley mode) (galerkin mode)

periodicGalerkinSupport :
  ∀ {Mode : Set} →
  (Mode → Bool) →
  (Mode → Bool) →
  List Mode →
  Nat →
  List Mode
periodicGalerkinSupport littlewoodPaley galerkin baseCube shell =
  Support.dyadicSupport
    (combinedPredicate littlewoodPaley galerkin)
    baseCube shell

periodicGalerkinSupportUniformBound :
  ∀ {Mode : Set}
    (littlewoodPaley galerkin : Mode → Bool)
    (baseCube : List Mode)
    (shell : Nat) →
  Support.countMass
    (periodicGalerkinSupport
      littlewoodPaley galerkin baseCube shell)
  ≤ Geo.pow Support.eight shell * Support.countMass baseCube
periodicGalerkinSupportUniformBound
  littlewoodPaley galerkin baseCube shell =
  Support.dyadicSupportCountBound
    (combinedPredicate littlewoodPaley galerkin)
    baseCube shell

-- Two different Galerkin cutoffs inherit the same shell capacity.  This is
-- the exact uniformity needed before a cutoff limit is taken.
record TwoCutoffUniformData (Mode : Set) : Set₁ where
  constructor two-cutoff-uniform-data
  field
    littlewoodPaley firstCutoff secondCutoff : Mode → Bool
    baseCube : List Mode
    shell : Nat

open TwoCutoffUniformData public

firstCutoffBound :
  ∀ {Mode : Set} (dataSet : TwoCutoffUniformData Mode) →
  Support.countMass
    (periodicGalerkinSupport
      (littlewoodPaley dataSet)
      (firstCutoff dataSet)
      (baseCube dataSet)
      (shell dataSet))
  ≤ Geo.pow Support.eight (shell dataSet)
    * Support.countMass (baseCube dataSet)
firstCutoffBound dataSet =
  periodicGalerkinSupportUniformBound
    (littlewoodPaley dataSet)
    (firstCutoff dataSet)
    (baseCube dataSet)
    (shell dataSet)

secondCutoffBound :
  ∀ {Mode : Set} (dataSet : TwoCutoffUniformData Mode) →
  Support.countMass
    (periodicGalerkinSupport
      (littlewoodPaley dataSet)
      (secondCutoff dataSet)
      (baseCube dataSet)
      (shell dataSet))
  ≤ Geo.pow Support.eight (shell dataSet)
    * Support.countMass (baseCube dataSet)
secondCutoffBound dataSet =
  periodicGalerkinSupportUniformBound
    (littlewoodPaley dataSet)
    (secondCutoff dataSet)
    (baseCube dataSet)
    (shell dataSet)
