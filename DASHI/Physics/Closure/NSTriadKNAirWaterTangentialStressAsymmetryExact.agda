module DASHI.Physics.Closure.NSTriadKNAirWaterTangentialStressAsymmetryExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Lev D. Landau; Evgeny M. Lifshitz.
-- Title: "Fluid Mechanics", Course of Theoretical Physics, Volume 6.
-- DOI: not assigned to the classical edition cited for the Newtonian stress
-- tensor and interfacial stress balance.
--
-- PURPOSE
-- Replace the speculative sign-inverted air/water mirror picture by the exact
-- algebra of a simple tangential-stress transmission model.  With constant
-- surface tension and no singular interfacial shear force,
--
--   mu_water g_water = mu_air g_air.
--
-- For the illustrative rational ratio mu_water/mu_air=50, matching stress
-- requires g_air=50 g_water.  The gradients have the same sign in this model;
-- stress continuity does not force an inverted vortex.  This is a deliberately
-- small exact transmission theorem, not a full moving-interface Navier--Stokes
-- construction with density jump, curvature and Marangoni terms.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (sym)

waterViscosity : ℚ
waterViscosity = Int.+ 50 / 1

airViscosity : ℚ
airViscosity = Int.+ 1 / 1

requiredAirGradient : ℚ → ℚ
requiredAirGradient waterGradient =
  waterViscosity * waterGradient

waterTangentialStress : ℚ → ℚ
waterTangentialStress waterGradient =
  waterViscosity * waterGradient

airTangentialStress : ℚ → ℚ
airTangentialStress airGradient =
  airViscosity * airGradient

stressTransmissionCloses :
  (waterGradient : ℚ) →
  waterTangentialStress waterGradient
  ≡ airTangentialStress (requiredAirGradient waterGradient)
stressTransmissionCloses waterGradient =
  solve (waterGradient ∷ [])

unitWaterGradient : ℚ
unitWaterGradient = Int.+ 1 / 1

sameSignUnitExample :
  requiredAirGradient unitWaterGradient ≡ Int.+ 50 / 1
sameSignUnitExample = solve []

noForcedSignInversion :
  airTangentialStress (requiredAirGradient unitWaterGradient)
  ≡ waterTangentialStress unitWaterGradient
noForcedSignInversion =
  sym (stressTransmissionCloses unitWaterGradient)
