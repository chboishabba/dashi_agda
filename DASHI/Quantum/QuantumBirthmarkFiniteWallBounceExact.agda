{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkFiniteWallBounceExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _/_; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Foundations.GRQFTNambuGotoTwoVacuumPotentialExact as Potential

data WallSite3 : Set where
  wallInterior : WallSite3
  wallBarrier : WallSite3
  wallExterior : WallSite3

wallField : WallSite3 → ℚ
wallField wallInterior = Potential.interiorField
wallField wallBarrier = Potential.barrierField
wallField wallExterior = Potential.exteriorField

wallPotential : WallSite3 → ℚ
wallPotential site = Potential.nambuVacuumPotential (wallField site)

wallInteriorEnergy :
  wallPotential wallInterior ≡ Int.+ 21 / 64
wallInteriorEnergy = Potential.interiorEnergy

wallExteriorEnergy :
  wallPotential wallExterior ≡ Int.+ 19 / 48
wallExteriorEnergy = Potential.exteriorEnergy

wallBarrierStationary :
  Potential.nambuVacuumPotentialPrime (wallField wallBarrier) ≡ 0ℚ
wallBarrierStationary = Potential.barrierStationary

wallInteriorStable :
  Potential.nambuVacuumPotentialSecond (wallField wallInterior)
  ≡ Int.+ 77 / 32
wallInteriorStable = Potential.interiorSecondDerivative

wallExteriorStable :
  Potential.nambuVacuumPotentialSecond (wallField wallExterior)
  ≡ Int.+ 51 / 32
wallExteriorStable = Potential.exteriorSecondDerivative

wallBarrierUnstable :
  Potential.nambuVacuumPotentialSecond (wallField wallBarrier)
  ≡ - (Int.+ 3927 / 4096)
wallBarrierUnstable = Potential.barrierSecondDerivative

finiteWallCarrierConstructed : Bool
finiteWallCarrierConstructed = true

continuumEulerLagrangeWallSolved : Bool
continuumEulerLagrangeWallSolved = false

bounceScaleFactor : ℚ → ℚ → ℚ
bounceScaleFactor a0 time = a0 + time * time

bouncePast : ℚ
bouncePast = - 1ℚ

bounceNow : ℚ
bounceNow = 0ℚ

bounceFuture : ℚ
bounceFuture = 1ℚ

pastScale : (a0 : ℚ) → bounceScaleFactor a0 bouncePast ≡ a0 + 1ℚ
pastScale a0 = solve (a0 ∷ [])

bounceMinimum : (a0 : ℚ) → bounceScaleFactor a0 bounceNow ≡ a0
bounceMinimum a0 = solve (a0 ∷ [])

futureScale : (a0 : ℚ) → bounceScaleFactor a0 bounceFuture ≡ a0 + 1ℚ
futureScale a0 = solve (a0 ∷ [])

incomingFiniteDifference :
  (a0 : ℚ) →
  bounceScaleFactor a0 bounceNow - bounceScaleFactor a0 bouncePast
  ≡ - 1ℚ
incomingFiniteDifference a0 = solve (a0 ∷ [])

outgoingFiniteDifference :
  (a0 : ℚ) →
  bounceScaleFactor a0 bounceFuture - bounceScaleFactor a0 bounceNow
  ≡ 1ℚ
outgoingFiniteDifference a0 = solve (a0 ∷ [])

positiveSecondDifference :
  (a0 : ℚ) →
  bounceScaleFactor a0 bounceFuture
    - (Int.+ 2 / 1) * bounceScaleFactor a0 bounceNow
    + bounceScaleFactor a0 bouncePast
  ≡ Int.+ 2 / 1
positiveSecondDifference a0 = solve (a0 ∷ [])

finiteBounceKinematicsConstructed : Bool
finiteBounceKinematicsConstructed = true

contractionToExpansionTurnaroundConstructed : Bool
contractionToExpansionTurnaroundConstructed = true

continuumFriedmannBounceSolutionConstructed : Bool
continuumFriedmannBounceSolutionConstructed = false

sameHistorySectorSourcesBounceDynamics : Bool
sameHistorySectorSourcesBounceDynamics = false
