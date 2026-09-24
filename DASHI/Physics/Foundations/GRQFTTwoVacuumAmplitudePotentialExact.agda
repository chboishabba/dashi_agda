{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTTwoVacuumAmplitudePotentialExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _/_; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Foundations.GRQFTDECRepulsiveExteriorMaxCutExact as MaxCut

------------------------------------------------------------------------
-- EXPLICIT TWO-VACUUM EFFECTIVE POTENTIAL
--
-- Let
--
--   W(phi) = phi^2 (1-phi)^2
--   h(phi) = 3 phi^2 - 2 phi^3
--
-- and
--
--   V(phi) = W(phi) + 21/64 + (3/64) h(phi).
--
-- The smoothstep tilt h changes the endpoint vacuum energies while preserving
-- stationarity at phi=0 and phi=1.
--
-- Expanded:
--
--   V(phi) = phi^4 - (67/32)phi^3 + (73/64)phi^2 + 21/64.
--
-- Formal derivative:
--
--   V'(phi) = phi(phi-1)(128phi-73)/32.
--
-- Therefore the critical points are 0, 73/128, 1.
------------------------------------------------------------------------

vacuumPotential :
  ℚ → ℚ
vacuumPotential phi =
  phi * phi * (1ℚ - phi) * (1ℚ - phi)
  + (Int.+ 21 / 64)
  + (Int.+ 3 / 64)
      * ((Int.+ 3 / 1) * phi * phi
        - (Int.+ 2 / 1) * phi * phi * phi)

vacuumPotentialExpanded :
  ℚ → ℚ
vacuumPotentialExpanded phi =
  phi * phi * phi * phi
  - (Int.+ 67 / 32) * phi * phi * phi
  + (Int.+ 73 / 64) * phi * phi
  + (Int.+ 21 / 64)

potentialExpansionIdentity :
  (phi : ℚ) →
  vacuumPotential phi ≡ vacuumPotentialExpanded phi
potentialExpansionIdentity phi =
  solve (phi ∷ [])

vacuumPotentialPrime :
  ℚ → ℚ
vacuumPotentialPrime phi =
  (Int.+ 73 / 32) * phi
  - (Int.+ 201 / 32) * phi * phi
  + (Int.+ 4 / 1) * phi * phi * phi

vacuumPotentialPrimeFactored :
  ℚ → ℚ
vacuumPotentialPrimeFactored phi =
  phi
  * (phi - 1ℚ)
  * ((Int.+ 128 / 1) * phi - (Int.+ 73 / 1))
  / (Int.+ 32 / 1)

potentialPrimeFactorization :
  (phi : ℚ) →
  vacuumPotentialPrime phi ≡ vacuumPotentialPrimeFactored phi
potentialPrimeFactorization phi =
  solve (phi ∷ [])

vacuumPotentialSecond :
  ℚ → ℚ
vacuumPotentialSecond phi =
  (Int.+ 73 / 32)
  - (Int.+ 201 / 16) * phi
  + (Int.+ 12 / 1) * phi * phi

------------------------------------------------------------------------
-- TWO REQUIRED VACUUM LEVELS
------------------------------------------------------------------------

interiorVacuumField : ℚ
interiorVacuumField = 0ℚ

exteriorVacuumField : ℚ
exteriorVacuumField = 1ℚ

barrierField : ℚ
barrierField = Int.+ 73 / 128

interiorVacuumEnergy :
  vacuumPotential interiorVacuumField ≡ Int.+ 21 / 64
interiorVacuumEnergy = refl

exteriorVacuumEnergy :
  vacuumPotential exteriorVacuumField ≡ Int.+ 3 / 8
exteriorVacuumEnergy = solve []

interiorStationary :
  vacuumPotentialPrime interiorVacuumField ≡ 0ℚ
interiorStationary = refl

exteriorStationary :
  vacuumPotentialPrime exteriorVacuumField ≡ 0ℚ
exteriorStationary = solve []

barrierStationary :
  vacuumPotentialPrime barrierField ≡ 0ℚ
barrierStationary = solve []

------------------------------------------------------------------------
-- LOCAL STABILITY / BARRIER CURVATURE DIAGNOSTICS
------------------------------------------------------------------------

interiorSecondDerivativePositiveValue :
  vacuumPotentialSecond interiorVacuumField ≡ Int.+ 73 / 32
interiorSecondDerivativePositiveValue = refl

exteriorSecondDerivativePositiveValue :
  vacuumPotentialSecond exteriorVacuumField ≡ Int.+ 55 / 32
exteriorSecondDerivativePositiveValue = solve []

barrierSecondDerivativeNegativeValue :
  vacuumPotentialSecond barrierField ≡ - (Int.+ 4015 / 4096)
barrierSecondDerivativeNegativeValue = solve []

------------------------------------------------------------------------
-- EXACT ENERGY FACTORIZATIONS
------------------------------------------------------------------------

interiorEnergyDifferenceFactor :
  ℚ → ℚ
interiorEnergyDifferenceFactor phi =
  phi * phi
  * ((Int.+ 64 / 1) * phi * phi
    - (Int.+ 134 / 1) * phi
    + (Int.+ 73 / 1))
  / (Int.+ 64 / 1)

interiorEnergyDifferenceFactorization :
  (phi : ℚ) →
  vacuumPotential phi - (Int.+ 21 / 64)
    ≡ interiorEnergyDifferenceFactor phi
interiorEnergyDifferenceFactorization phi =
  solve (phi ∷ [])

exteriorEnergyDifferenceFactor :
  ℚ → ℚ
exteriorEnergyDifferenceFactor phi =
  (phi - 1ℚ) * (phi - 1ℚ)
  * ((Int.+ 64 / 1) * phi * phi
    - (Int.+ 6 / 1) * phi
    - (Int.+ 3 / 1))
  / (Int.+ 64 / 1)

exteriorEnergyDifferenceFactorization :
  (phi : ℚ) →
  vacuumPotential phi - (Int.+ 3 / 8)
    ≡ exteriorEnergyDifferenceFactor phi
exteriorEnergyDifferenceFactorization phi =
  solve (phi ∷ [])

------------------------------------------------------------------------
-- AMPLITUDE MODEL RECEIPT
------------------------------------------------------------------------

record TwoVacuumAmplitudePotentialWitness : Set where
  constructor two-vacuum-amplitude-potential-witness
  field
    interiorEnergy :
      vacuumPotential interiorVacuumField ≡ Int.+ 21 / 64

    exteriorEnergy :
      vacuumPotential exteriorVacuumField ≡ Int.+ 3 / 8

    interiorCritical :
      vacuumPotentialPrime interiorVacuumField ≡ 0ℚ

    exteriorCritical :
      vacuumPotentialPrime exteriorVacuumField ≡ 0ℚ

    barrierCritical :
      vacuumPotentialPrime barrierField ≡ 0ℚ

    interiorCurvature :
      vacuumPotentialSecond interiorVacuumField ≡ Int.+ 73 / 32

    exteriorCurvature :
      vacuumPotentialSecond exteriorVacuumField ≡ Int.+ 55 / 32

    barrierCurvature :
      vacuumPotentialSecond barrierField ≡ - (Int.+ 4015 / 4096)

open TwoVacuumAmplitudePotentialWitness public

canonicalTwoVacuumAmplitudePotentialWitness :
  TwoVacuumAmplitudePotentialWitness
canonicalTwoVacuumAmplitudePotentialWitness =
  two-vacuum-amplitude-potential-witness
    interiorVacuumEnergy
    exteriorVacuumEnergy
    interiorStationary
    exteriorStationary
    barrierStationary
    interiorSecondDerivativePositiveValue
    exteriorSecondDerivativePositiveValue
    barrierSecondDerivativeNegativeValue

twoVacuumAmplitudeModelReceipt :
  MaxCut.CMP119VacuumAmplitudeModelReceipt
twoVacuumAmplitudeModelReceipt =
  MaxCut.cmp119-vacuum-amplitude-model-receipt
    (Int.+ 21 / 64)
    (Int.+ 3 / 8)
    refl
    refl
    TwoVacuumAmplitudePotentialWitness
    canonicalTwoVacuumAmplitudePotentialWitness

record TwoVacuumAmplitudePotentialBoundary : Set where
  constructor two-vacuum-amplitude-potential-boundary
  field
    exactInteriorAmplitudeProduced : Bool
    exactExteriorAmplitudeProduced : Bool
    bothEndpointStationary : Bool
    bothEndpointPositiveSecondDerivative : Bool
    separatingBarrierStationary : Bool
    barrierNegativeSecondDerivative : Bool
    sourceNativeCMP119PotentialDerived : Bool
    continuumDomainWallSolutionConstructed : Bool
    quantumTunnelingRateConstructed : Bool

canonicalTwoVacuumAmplitudePotentialBoundary :
  TwoVacuumAmplitudePotentialBoundary
canonicalTwoVacuumAmplitudePotentialBoundary =
  two-vacuum-amplitude-potential-boundary
    true true true true true true false false false
