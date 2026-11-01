{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTNambuGotoSurfaceActionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; -_)

------------------------------------------------------------------------
-- POSITIVE-TENSION NAMBU-GOTO SURFACE SOURCE
--
-- A Nambu-Goto membrane action
--
--   S_shell = -tau ∫ sqrt(-h) d^3xi
--
-- carries orthonormal surface stress
--
--   sigma = +tau
--   P     = -tau.
--
-- Work with the exact 8*pi-scaled tension coordinate
--
--   tau8 = 8*pi*tau.
--
-- For the R=2 member of the repulsive shell family:
--
--   tau8 = 1/4,
--
-- matching the Israel shell:
--
--   8*pi*sigma = +1/4
--   8*pi*P     = -1/4.
------------------------------------------------------------------------

record NambuGotoSurfaceSource : Set where
  constructor nambu-goto-surface-source
  field
    tension8Pi : ℚ

open NambuGotoSurfaceSource public

surfaceSigma8Pi :
  NambuGotoSurfaceSource → ℚ
surfaceSigma8Pi source =
  tension8Pi source

surfacePressure8Pi :
  NambuGotoSurfaceSource → ℚ
surfacePressure8Pi source =
  - (tension8Pi source)

fixtureSurfaceSource :
  NambuGotoSurfaceSource
fixtureSurfaceSource =
  nambu-goto-surface-source (Int.+ 1 / 4)

fixtureSurfaceSigma :
  surfaceSigma8Pi fixtureSurfaceSource ≡ Int.+ 1 / 4
fixtureSurfaceSigma = refl

fixtureSurfacePressure :
  surfacePressure8Pi fixtureSurfaceSource ≡ - (Int.+ 1 / 4)
fixtureSurfacePressure = refl

fixtureDomainWallEquationOfState :
  surfacePressure8Pi fixtureSurfaceSource
    ≡ - (surfaceSigma8Pi fixtureSurfaceSource)
fixtureDomainWallEquationOfState = refl

------------------------------------------------------------------------
-- FAMILY SCALING
--
-- The shell family has
--
--   8*pi*sigma = 1/(2R).
--
-- Avoiding a variable-denominator theorem in this Agda lane, represent the
-- exact denominator-cleared relation
--
--   2 R tau8 = 1.
------------------------------------------------------------------------

record RadiusTensionLaw (radius : ℚ) : Set where
  constructor radius-tension-law
  field
    tension8Pi : ℚ
    denominatorClearedLaw :
      (Int.+ 2 / 1) * radius * tension8Pi ≡ Int.+ 1 / 1

open RadiusTensionLaw public

fixtureRadiusTensionLaw :
  RadiusTensionLaw (Int.+ 2 / 1)
fixtureRadiusTensionLaw =
  radius-tension-law
    (Int.+ 1 / 4)
    refl

record NambuGotoSurfaceActionBoundary : Set where
  constructor nambu-goto-surface-action-boundary
  field
    positiveTensionSurfaceModelConstructed : Bool
    shellEnergyDensityPositive : Bool
    shellPressureIsNegativeTension : Bool
    domainWallEquationOfStateExact : Bool
    negativeSurfaceEnergyRequired : Bool
    sourceDerivedFromCMP119YMAction : Bool
    finiteThicknessWallDerived : Bool

canonicalNambuGotoSurfaceActionBoundary :
  NambuGotoSurfaceActionBoundary
canonicalNambuGotoSurfaceActionBoundary =
  nambu-goto-surface-action-boundary
    true true true true false false false
