{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.PositiveGConservedAnisotropicProfileCompilerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _-_; _*_; _/_)
import Data.Integer.Base as Int
open import Data.Rational.Tactic.RingSolver using (solve-∀)

import DASHI.Physics.Foundations.PositiveGAnisotropicTOVConservationExact as TOV

half : ℚ
half = Int.+ 1 / 2

conservationCore : ℚ → ℚ → ℚ → ℚ → ℚ
conservationCore rho pr prPrime phiPrime =
  prPrime + (rho + pr) * phiPrime

tangentialPressureFromConservation :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
tangentialPressureFromConservation rho pr prPrime phiPrime radius =
  pr + half * radius * conservationCore rho pr prPrime phiPrime

activeSource : ℚ → ℚ → ℚ → ℚ
activeSource rho pr pt = rho + pr + pt + pt

conservationResidualFactorization :
  ∀ rho pr prPrime phiPrime radius inverseRadius →
  TOV.anisotropicConservationResidual
    rho pr
    (tangentialPressureFromConservation rho pr prPrime phiPrime radius)
    prPrime phiPrime inverseRadius
  ≡
  conservationCore rho pr prPrime phiPrime
    * (1ℚ - radius * inverseRadius)
conservationResidualFactorization = solve-∀

activeSourceAfterConservationCompiler :
  ∀ rho pr prPrime phiPrime radius →
  activeSource rho pr
    (tangentialPressureFromConservation rho pr prPrime phiPrime radius)
  ≡
  rho + pr + pr + pr
    + radius * conservationCore rho pr prPrime phiPrime
activeSourceAfterConservationCompiler = solve-∀

record ConservedAnisotropicProfileCompilerBoundary : Set where
  constructor conserved-anisotropic-profile-compiler-boundary
  field
    tangentialPressureNoLongerIndependentUnknown : Bool
    conservationResidualFactorized : Bool
    inverseRadiusIdentityClosesConservation : Bool
    activeSourceReducedToRhoPrPhiPrime : Bool
    coupledEinsteinEquationStillMustBeSolved : Bool
    boundaryAndGlobalMassConditionsStillMustBeSolved : Bool

canonicalConservedAnisotropicProfileCompilerBoundary :
  ConservedAnisotropicProfileCompilerBoundary
canonicalConservedAnisotropicProfileCompilerBoundary =
  conserved-anisotropic-profile-compiler-boundary
    true true true true true true
