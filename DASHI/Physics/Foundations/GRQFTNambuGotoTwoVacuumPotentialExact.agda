{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTNambuGotoTwoVacuumPotentialExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _/_; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

------------------------------------------------------------------------
-- TWO-VACUUM POTENTIAL MATCHED TO THE NAMBU-GOTO SHELL FAMILY
--
-- At R=2 the exact shell family requires
--
--   Lambda_in  = 21/64
--   Lambda_out = 19/48.
--
-- Use
--
--   V(phi)
--     = phi^2(1-phi)^2
--       + 21/64
--       + (13/192)(3phi^2-2phi^3).
--
-- Then
--
--   V(0)=21/64
--   V(1)=19/48
--
-- while both endpoints remain stationary and locally stable.
------------------------------------------------------------------------

nambuVacuumPotential :
  ℚ → ℚ
nambuVacuumPotential phi =
  phi * phi * (1ℚ - phi) * (1ℚ - phi)
  + (Int.+ 21 / 64)
  + (Int.+ 13 / 192)
      * ((Int.+ 3 / 1) * phi * phi
        - (Int.+ 2 / 1) * phi * phi * phi)

nambuVacuumPotentialPrime :
  ℚ → ℚ
nambuVacuumPotentialPrime phi =
  (Int.+ 77 / 32) * phi
  - (Int.+ 205 / 32) * phi * phi
  + (Int.+ 4 / 1) * phi * phi * phi

nambuVacuumPotentialPrimeFactored :
  ℚ → ℚ
nambuVacuumPotentialPrimeFactored phi =
  phi
  * (phi - 1ℚ)
  * ((Int.+ 128 / 1) * phi - (Int.+ 77 / 1))
  / (Int.+ 32 / 1)

nambuPrimeFactorization :
  (phi : ℚ) →
  nambuVacuumPotentialPrime phi
    ≡ nambuVacuumPotentialPrimeFactored phi
nambuPrimeFactorization phi =
  solve (phi ∷ [])

nambuVacuumPotentialSecond :
  ℚ → ℚ
nambuVacuumPotentialSecond phi =
  (Int.+ 77 / 32)
  - (Int.+ 205 / 16) * phi
  + (Int.+ 12 / 1) * phi * phi

interiorField : ℚ
interiorField = 0ℚ

exteriorField : ℚ
exteriorField = 1ℚ

barrierField : ℚ
barrierField = Int.+ 77 / 128

interiorEnergy :
  nambuVacuumPotential interiorField ≡ Int.+ 21 / 64
interiorEnergy = refl

exteriorEnergy :
  nambuVacuumPotential exteriorField ≡ Int.+ 19 / 48
exteriorEnergy = solve []

interiorStationary :
  nambuVacuumPotentialPrime interiorField ≡ 0ℚ
interiorStationary = refl

exteriorStationary :
  nambuVacuumPotentialPrime exteriorField ≡ 0ℚ
exteriorStationary = solve []

barrierStationary :
  nambuVacuumPotentialPrime barrierField ≡ 0ℚ
barrierStationary = solve []

interiorSecondDerivative :
  nambuVacuumPotentialSecond interiorField ≡ Int.+ 77 / 32
interiorSecondDerivative = refl

exteriorSecondDerivative :
  nambuVacuumPotentialSecond exteriorField ≡ Int.+ 51 / 32
exteriorSecondDerivative = solve []

barrierSecondDerivative :
  nambuVacuumPotentialSecond barrierField
    ≡ - (Int.+ 3927 / 4096)
barrierSecondDerivative = solve []

------------------------------------------------------------------------
-- EXACT ENERGY FACTORIZATIONS
------------------------------------------------------------------------

interiorDifferenceFactor :
  ℚ → ℚ
interiorDifferenceFactor phi =
  phi * phi
  * ((Int.+ 192 / 1) * phi * phi
    - (Int.+ 410 / 1) * phi
    + (Int.+ 231 / 1))
  / (Int.+ 192 / 1)

interiorDifferenceFactorization :
  (phi : ℚ) →
  nambuVacuumPotential phi - (Int.+ 21 / 64)
    ≡ interiorDifferenceFactor phi
interiorDifferenceFactorization phi =
  solve (phi ∷ [])

exteriorDifferenceFactor :
  ℚ → ℚ
exteriorDifferenceFactor phi =
  (phi - 1ℚ) * (phi - 1ℚ)
  * ((Int.+ 192 / 1) * phi * phi
    - (Int.+ 26 / 1) * phi
    - (Int.+ 13 / 1))
  / (Int.+ 192 / 1)

exteriorDifferenceFactorization :
  (phi : ℚ) →
  nambuVacuumPotential phi - (Int.+ 19 / 48)
    ≡ exteriorDifferenceFactor phi
exteriorDifferenceFactorization phi =
  solve (phi ∷ [])

------------------------------------------------------------------------
-- SCALING THE WHOLE POTENTIAL
--
-- The one-parameter shell family requires both vacuum amplitudes to scale
-- together as 1/R^2.  Multiplying the whole potential by a scalar preserves
-- the critical-point locations and scales both vacuum energies identically.
------------------------------------------------------------------------

scaledNambuPotential :
  ℚ → ℚ → ℚ
scaledNambuPotential scale phi =
  scale * nambuVacuumPotential phi

scaledInteriorEnergy :
  (scale : ℚ) →
  scaledNambuPotential scale interiorField
    ≡ scale * (Int.+ 21 / 64)
scaledInteriorEnergy scale = refl

scaledExteriorEnergy :
  (scale : ℚ) →
  scaledNambuPotential scale exteriorField
    ≡ scale * (Int.+ 19 / 48)
scaledExteriorEnergy scale =
  solve (scale ∷ [])

record NambuGotoTwoVacuumPotentialWitness : Set where
  constructor nambu-goto-two-vacuum-potential-witness
  field
    interiorVacuum :
      nambuVacuumPotential interiorField ≡ Int.+ 21 / 64

    exteriorVacuum :
      nambuVacuumPotential exteriorField ≡ Int.+ 19 / 48

    interiorCritical :
      nambuVacuumPotentialPrime interiorField ≡ 0ℚ

    exteriorCritical :
      nambuVacuumPotentialPrime exteriorField ≡ 0ℚ

    barrierCritical :
      nambuVacuumPotentialPrime barrierField ≡ 0ℚ

    interiorStableCurvature :
      nambuVacuumPotentialSecond interiorField ≡ Int.+ 77 / 32

    exteriorStableCurvature :
      nambuVacuumPotentialSecond exteriorField ≡ Int.+ 51 / 32

    barrierUnstableCurvature :
      nambuVacuumPotentialSecond barrierField
        ≡ - (Int.+ 3927 / 4096)

open NambuGotoTwoVacuumPotentialWitness public

canonicalNambuGotoTwoVacuumPotentialWitness :
  NambuGotoTwoVacuumPotentialWitness
canonicalNambuGotoTwoVacuumPotentialWitness =
  nambu-goto-two-vacuum-potential-witness
    interiorEnergy
    exteriorEnergy
    interiorStationary
    exteriorStationary
    barrierStationary
    interiorSecondDerivative
    exteriorSecondDerivative
    barrierSecondDerivative

record NambuGotoTwoVacuumPotentialBoundary : Set where
  constructor nambu-goto-two-vacuum-potential-boundary
  field
    exactNambuInteriorVacuumProduced : Bool
    exactNambuExteriorVacuumProduced : Bool
    bothEndpointStationary : Bool
    bothEndpointPositiveSecondDerivative : Bool
    separatingBarrierConstructed : Bool
    uniformPotentialScalingPreservesVacuumRatio : Bool
    sourceNativeCMP119PotentialDerived : Bool
    continuumGravitatingBubbleSolutionDerived : Bool

canonicalNambuGotoTwoVacuumPotentialBoundary :
  NambuGotoTwoVacuumPotentialBoundary
canonicalNambuGotoTwoVacuumPotentialBoundary =
  nambu-goto-two-vacuum-potential-boundary
    true true true true true true false false
