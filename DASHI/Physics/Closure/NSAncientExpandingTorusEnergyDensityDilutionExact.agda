module DASHI.Physics.Closure.NSAncientExpandingTorusEnergyDensityDilutionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Gabriel Koch; Nikolai Nadirashvili; Gregory A. Seregin;
--          Vladimir Sverak.
-- Title: "Liouville theorems for the Navier-Stokes equations and applications".
-- DOI: 10.1007/s11511-009-0039-6.
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- ROUND65 / WHAT PERIODIC ANCESTRY RETAINS AFTER DECOMPACTIFICATION
--
-- Under the KNSŠ velocity blow-up
--
--   u_M(y) = M^(-1) u(x0 + y/M),
--
-- a three-dimensional period cell has volume factor M^3.  Velocity squared
-- contributes M^(-2), hence full-cell L2 mass has factor M, while the
-- mean-square energy DENSITY has factor M^(-2).  The cell mean velocity has
-- factor M^(-1).
--
-- Therefore, for M -> infinity,
--
--   rescaled box mean          -> 0,
--   rescaled mean-square density -> 0,
--
-- even though local convergence may retain a nonzero normalized maximum.
-- This is genuine periodic ancestry, but by itself it is not a local-limit
-- theorem: compensation/dilution may escape to distances comparable to the
-- expanding period.  Round65's flat-plateau falsifier exhibits that seam.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

square : ℚ → ℚ
square x = x * x

cube : ℚ → ℚ
cube x = x * square x

scaledCellVolumeFactor : ℚ → ℚ
scaledCellVolumeFactor amplitude = cube amplitude

scaledCellL2MassFactor : ℚ → ℚ → ℚ
scaledCellL2MassFactor inverseAmplitude amplitude =
  square inverseAmplitude * cube amplitude

inverseScaledCellVolumeFactor : ℚ → ℚ
inverseScaledCellVolumeFactor inverseAmplitude = cube inverseAmplitude

scaledCellMeanSquareDensityFactor : ℚ → ℚ → ℚ
scaledCellMeanSquareDensityFactor inverseAmplitude amplitude =
  scaledCellL2MassFactor inverseAmplitude amplitude
  * inverseScaledCellVolumeFactor inverseAmplitude

scaledCellMeanVelocityFactor : ℚ → ℚ
scaledCellMeanVelocityFactor inverseAmplitude = inverseAmplitude

squareInverseProduct :
  (inverseAmplitude amplitude : ℚ) →
  inverseAmplitude * amplitude ≡ 1ℚ →
  square inverseAmplitude * square amplitude ≡ 1ℚ
squareInverseProduct inverseAmplitude amplitude inverse =
  trans
    (solve (inverseAmplitude ∷ amplitude ∷ []))
    (cong square inverse)

cubeInverseProduct :
  (inverseAmplitude amplitude : ℚ) →
  inverseAmplitude * amplitude ≡ 1ℚ →
  cube inverseAmplitude * cube amplitude ≡ 1ℚ
cubeInverseProduct inverseAmplitude amplitude inverse =
  trans
    (solve (inverseAmplitude ∷ amplitude ∷ []))
    (cong cube inverse)

fullCellL2MassGrowsOnlyLinearly :
  (inverseAmplitude amplitude : ℚ) →
  inverseAmplitude * amplitude ≡ 1ℚ →
  scaledCellL2MassFactor inverseAmplitude amplitude ≡ amplitude
fullCellL2MassGrowsOnlyLinearly inverseAmplitude amplitude inverse =
  let
    regroup :
      scaledCellL2MassFactor inverseAmplitude amplitude
      ≡ (square inverseAmplitude * square amplitude) * amplitude
    regroup = solve (inverseAmplitude ∷ amplitude ∷ [])
  in
  trans regroup
    (trans
      (cong (_* amplitude) (squareInverseProduct inverseAmplitude amplitude inverse))
      (solve (amplitude ∷ [])))

meanSquareDensityDecaysByInverseAmplitudeSquared :
  (inverseAmplitude amplitude : ℚ) →
  inverseAmplitude * amplitude ≡ 1ℚ →
  scaledCellMeanSquareDensityFactor inverseAmplitude amplitude
  ≡ square inverseAmplitude
meanSquareDensityDecaysByInverseAmplitudeSquared
    inverseAmplitude amplitude inverse =
  let
    regroup :
      scaledCellMeanSquareDensityFactor inverseAmplitude amplitude
      ≡ square inverseAmplitude
        * (cube amplitude * cube inverseAmplitude)
    regroup = solve (inverseAmplitude ∷ amplitude ∷ [])

    cubeCancel : cube amplitude * cube inverseAmplitude ≡ 1ℚ
    cubeCancel =
      trans
        (solve (inverseAmplitude ∷ amplitude ∷ []))
        (cubeInverseProduct inverseAmplitude amplitude inverse)
  in
  trans regroup
    (trans (cong (square inverseAmplitude *_) cubeCancel)
      (solve (inverseAmplitude ∷ [])))

-- The limiting statements as inverseAmplitude -> 0 are Archimedean/analytic
-- consequences.  This exact file owns the scaling identities only.
