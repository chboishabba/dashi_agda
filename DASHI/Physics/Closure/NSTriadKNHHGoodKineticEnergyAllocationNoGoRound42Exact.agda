module DASHI.Physics.Closure.NSTriadKNHHGoodKineticEnergyAllocationNoGoRound42Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: J. Thomas Beale; Tosio Kato; Andrew Majda.
-- Title: "Remarks on the Breakdown of Smooth Solutions for the 3-D Euler
-- Equations".
-- Communications in Mathematical Physics 94 (1984), 61--66.
-- DOI: 10.1007/BF01240221.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Round 42's literal amplitude allocation correctly says that the degree-six
-- HH-good weight can be written as one quadratic amplitude square times one
-- quartic core.  But the amplitudes in `PhysicalVorticityPair` are vorticity
-- amplitudes, not velocity amplitudes.  Therefore the suggestion that the
-- selected square might be bounded directly by the conserved kinetic energy
-- E0 must itself pass a derivative-scaling audit.
--
-- The repository's exact Biot--Savart theorem already gives, for a transverse
-- nonzero Fourier vorticity mode,
--
--   |u_k|^2 = |k|^-2 |omega_k|^2.
--
-- This file rearranges that same-object identity to
--
--   |omega_k|^2 = |k|^2 |u_k|^2.
--
-- Hence a modewise kinetic-energy bound `|u_k|^2 <= E0` yields only
--
--   |omega_k|^2 <= |k|^2 E0,
--
-- not a shell-independent `|omega_k|^2 <= E0`.
--
-- A concrete exact mode k=(2,0,0), omega=(0,0,-2) has
--
--   u = B_k omega = (0,1,0),
--   |u|^2 = 1,
--   |omega|^2 = 4.
--
-- Thus bare kinetic energy cannot be the missing quadratic HH-good resource
-- without an additional inverse-derivative/shell compensation elsewhere.
-- The viable Round-42 amplitude allocation remains useful, but its physical
-- `dataEnergyFactor` must be a genuinely compatible controlled quantity, or
-- the residual quartic estimate must return the lost |k|^-2 factor exactly.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _*_; _≤_; _<_; -_ ; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNFourierBiotSavartExact as BS

vorticityNormFromBiotSavartVelocity :
  (modeData : V.ProjectionMode) →
  (omega : V.Vector3) →
  V.dot (V.mode modeData) omega ≡ 0ℚ →
  V.normSquared omega
  ≡ V.normSquared (V.mode modeData)
      * V.normSquared (BS.biotSavart modeData omega)
vorticityNormFromBiotSavartVelocity modeData omega transverse =
  let
    modeNorm = V.normSquared (V.mode modeData)
    inverse = V.inverseNormSquared modeData
    omegaNorm = V.normSquared omega
    velocityNorm = V.normSquared (BS.biotSavart modeData omega)

    velocityMeaning : velocityNorm ≡ inverse * omegaNorm
    velocityMeaning = BS.biotSavartNormGainSquared modeData omega transverse

    scaled : modeNorm * velocityNorm ≡ modeNorm * (inverse * omegaNorm)
    scaled = cong (modeNorm *_) velocityMeaning

    regroup :
      modeNorm * (inverse * omegaNorm)
      ≡ (inverse * modeNorm) * omegaNorm
    regroup = solve (modeNorm ∷ inverse ∷ omegaNorm ∷ [])

    cancel : (inverse * modeNorm) * omegaNorm ≡ omegaNorm
    cancel =
      trans
        (cong (_* omegaNorm) (V.inverseLaw modeData))
        (solve (omegaNorm ∷ []))
  in
  sym (trans scaled (trans regroup cancel))

kineticModeEnergyOnlyGivesFrequencyWeightedVorticityBound :
  (modeData : V.ProjectionMode) →
  (omega : V.Vector3) →
  V.dot (V.mode modeData) omega ≡ 0ℚ →
  (E0 : ℚ) →
  V.normSquared (BS.biotSavart modeData omega) ≤ E0 →
  V.normSquared omega
  ≤ V.normSquared (V.mode modeData) * E0
kineticModeEnergyOnlyGivesFrequencyWeightedVorticityBound
    modeData omega transverse E0 velocityBelowE0 =
  let
    modeNorm = V.normSquared (V.mode modeData)
    modeNormNN = V.normSquaredNonnegative (V.mode modeData)

    scaled :
      modeNorm * V.normSquared (BS.biotSavart modeData omega)
      ≤ modeNorm * E0
    scaled =
      let instance modeNormNNI = nonNegative modeNormNN
      in ℚP.*-monoˡ-≤-nonNeg modeNorm velocityBelowE0
  in
  subst
    (λ lower → lower ≤ modeNorm * E0)
    (sym (vorticityNormFromBiotSavartVelocity modeData omega transverse))
    scaled

------------------------------------------------------------------------
-- Explicit rational counterexample to the bare `vorticity square <= E0` idea.
------------------------------------------------------------------------

two four quarter : ℚ
two = Int.+ 2 / 1
four = Int.+ 4 / 1
quarter = Int.+ 1 / 4

modeTwo : V.ProjectionMode
modeTwo = V.projection-mode (V.v3 two 0ℚ 0ℚ) quarter inverseLaw
  where
  inverseLaw :
    quarter * V.normSquared (V.v3 two 0ℚ 0ℚ) ≡ 1ℚ
  inverseLaw = solve (two ∷ quarter ∷ [])

omegaTwo : V.Vector3
omegaTwo = V.v3 0ℚ 0ℚ (- two)

velocityTwo : V.Vector3
velocityTwo = BS.biotSavart modeTwo omegaTwo

omegaTwoTransverse :
  V.dot (V.mode modeTwo) omegaTwo ≡ 0ℚ
omegaTwoTransverse = solve (two ∷ [])

velocityTwoCoordinates : velocityTwo ≡ V.v3 0ℚ 1ℚ 0ℚ
velocityTwoCoordinates =
  V.vectorExt
    (solve (two ∷ quarter ∷ []))
    (solve (two ∷ quarter ∷ []))
    (solve (two ∷ quarter ∷ []))

velocityTwoNormSquared : V.normSquared velocityTwo ≡ 1ℚ
velocityTwoNormSquared =
  trans
    (cong V.normSquared velocityTwoCoordinates)
    (solve [])

omegaTwoNormSquared : V.normSquared omegaTwo ≡ four
omegaTwoNormSquared = solve (two ∷ four ∷ [])

oneLessFour : 1ℚ < four
oneLessFour = toWitness {a? = 1ℚ ℚP.<? four} _

bareKineticEnergyDoesNotBoundVorticityAmplitude :
  ¬ (V.normSquared omegaTwo ≤ V.normSquared velocityTwo)
bareKineticEnergyDoesNotBoundVorticityAmplitude alleged =
  let
    fourBelowOne : four ≤ 1ℚ
    fourBelowOne =
      subst
        (λ lower → lower ≤ 1ℚ)
        omegaTwoNormSquared
        (subst
          (λ upper → V.normSquared omegaTwo ≤ upper)
          velocityTwoNormSquared
          alleged)

    fourLessFour : four < four
    fourLessFour = ℚP.≤-<-trans fourBelowOne oneLessFour
  in
  ℚP.<-irrefl refl fourLessFour

hhGoodBareKineticEnergyAllocationRefuted : Bool
hhGoodBareKineticEnergyAllocationRefuted = true

hhGoodAmplitudeAllocationNeedsCompatibleQuadraticResource : Bool
hhGoodAmplitudeAllocationNeedsCompatibleQuadraticResource = true

hhGoodBareKineticEnergyAllocationRefutedIsTrue :
  hhGoodBareKineticEnergyAllocationRefuted ≡ true
hhGoodBareKineticEnergyAllocationRefutedIsTrue = refl
