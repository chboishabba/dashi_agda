module DASHI.Physics.Closure.NSTriadKNPeriodicScalingFrameProductNoGoRound77Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Authors: Jindrich Necas; Michael Ruzicka; Vladimir Sverak.
-- Title: "On Leray's self-similar solutions of the Navier-Stokes equations".
-- Acta Mathematica 176 (1996), 283--294.
-- DOI: 10.1007/BF02551584.
--
-- Author: Tai-Peng Tsai.
-- Title: "On Leray's self-similar solutions of the Navier-Stokes equations
-- satisfying local energy estimates".
-- Archive for Rational Mechanics and Analysis 143 (1998), 29--51.
-- DOI: 10.1007/s002050050099.
--
-- ROUND77 / PERIODIC-SCALING NORMALIZATION AUDIT
--
-- The Euclidean Navier--Stokes scaling
--
--   u_lambda(x,t) = lambda u(lambda x, lambda^2 t)
--
-- is indispensable in blowup analysis, but on a FIXED periodic torus it is
-- not a free amplitude gauge.  For an integer torus dilation lambda, normalized
-- torus L2 energy scales by lambda^2, and the corresponding Fourier mode energy
-- also scales by lambda^2.  Therefore the Round75/76 literal frame product
--
--   B_k = ||u_k||^2 E_N
--
-- has scaling degree FOUR:
--
--   B_{lambda k}[u_lambda] = lambda^4 B_k[u].
--
-- In particular, upward dyadic shell dilation cannot justify replacing an
-- arbitrary physical B_k by the unit hypothesis B_k <= 1.  Inverse dilation
-- changes the fixed periodic carrier unless extra covering/base-change data are
-- supplied.  Round77 therefore carries a reciprocal frame weight explicitly
-- instead of treating unit normalization as a scale choice.
--
-- NRS/Tsai are cited only for self-similar rigidity context.  Their whole-space
-- Liouville theorems do not supply this finite periodic arithmetic and are not
-- used as a positivity theorem for the DASHI propagation tree.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

square : ℚ → ℚ
square x = x * x

fourth : ℚ → ℚ
fourth x = square (square x)

frameProduct : ℚ → ℚ → ℚ
frameProduct modeEnergy cutoffEnergy = modeEnergy * cutoffEnergy

scaledModeEnergy : ℚ → ℚ → ℚ
scaledModeEnergy lambda modeEnergy = square lambda * modeEnergy

scaledCutoffEnergy : ℚ → ℚ → ℚ
scaledCutoffEnergy lambda cutoffEnergy = square lambda * cutoffEnergy

scaledFrameProduct : ℚ → ℚ → ℚ → ℚ
scaledFrameProduct lambda modeEnergy cutoffEnergy =
  frameProduct
    (scaledModeEnergy lambda modeEnergy)
    (scaledCutoffEnergy lambda cutoffEnergy)

periodicDilationFrameProductHasDegreeFour :
  ∀ lambda modeEnergy cutoffEnergy →
  scaledFrameProduct lambda modeEnergy cutoffEnergy
  ≡ fourth lambda * frameProduct modeEnergy cutoffEnergy
periodicDilationFrameProductHasDegreeFour lambda modeEnergy cutoffEnergy =
  solve (lambda ∷ modeEnergy ∷ cutoffEnergy ∷ [])

-- A concrete dyadic witness: lambda=2 multiplies B by 16.  This is an exact
-- arithmetic falsifier for the idea that upward dyadic zoom leaves B unchanged
-- or automatically normalizes it to one.
two : ℚ
two = 1ℚ + 1ℚ

dyadicFrameProductFactorSixteen :
  ∀ modeEnergy cutoffEnergy →
  scaledFrameProduct two modeEnergy cutoffEnergy
  ≡ (two * two * two * two) * frameProduct modeEnergy cutoffEnergy
dyadicFrameProductFactorSixteen modeEnergy cutoffEnergy =
  solve (modeEnergy ∷ cutoffEnergy ∷ [])

unitModeTwoEnergyOriginalProduct :
  frameProduct 1ℚ two ≡ two
unitModeTwoEnergyOriginalProduct = solve []

unitModeTwoEnergyDyadicProduct :
  scaledFrameProduct two 1ℚ two
  ≡ two * two * two * two * two
unitModeTwoEnergyDyadicProduct = solve []

round77FixedTorusUpwardDilationPreservesFrameProduct : Bool
round77FixedTorusUpwardDilationPreservesFrameProduct = false

round77FixedTorusFrameProductHasScalingDegreeFour : Bool
round77FixedTorusFrameProductHasScalingDegreeFour = true

round77UnitFrameBoundMayBeAssumedByDyadicZoom : Bool
round77UnitFrameBoundMayBeAssumedByDyadicZoom = false

round77ReciprocalFrameWeightMustRemainExplicit : Bool
round77ReciprocalFrameWeightMustRemainExplicit = true

round77FixedTorusFrameProductHasScalingDegreeFourIsTrue :
  round77FixedTorusFrameProductHasScalingDegreeFour ≡ true
round77FixedTorusFrameProductHasScalingDegreeFourIsTrue = refl

round77UnitFrameBoundMayBeAssumedByDyadicZoomIsFalse :
  round77UnitFrameBoundMayBeAssumedByDyadicZoom ≡ false
round77UnitFrameBoundMayBeAssumedByDyadicZoomIsFalse = refl
