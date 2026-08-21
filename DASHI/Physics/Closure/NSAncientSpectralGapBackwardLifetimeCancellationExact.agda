module DASHI.Physics.Closure.NSAncientSpectralGapBackwardLifetimeCancellationExact where

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
-- ROUND65 / MOVING SPECTRAL-GAP NO-FREE-LUNCH
--
-- A fixed periodic box has a positive Poincare/Laplacian spectral gap.  Under
-- KNSŠ blow-up by amplitude M, the period grows by M, so the gap scales by
-- M^(-2).  The available backward lifetime from a fixed original starting
-- time scales by M^2.  Their product is therefore EXACTLY scale invariant:
--
--   (M^(-2) lambda_0) * (M^2 A_0) = lambda_0 A_0.
--
-- Thus decompactification and ancient-time growth cancel at this elementary
-- level.  One cannot recover the fixed-torus Liouville exponential damping
-- merely by observing that the rescaled solution exists farther into the
-- past.  A positive whole-space rigidity argument needs additional structure.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

square : ℚ → ℚ
square x = x * x

rescaledGap : ℚ → ℚ → ℚ
rescaledGap inverseAmplitude baseGap =
  square inverseAmplitude * baseGap

rescaledBackwardLifetime : ℚ → ℚ → ℚ
rescaledBackwardLifetime amplitude baseLifetime =
  square amplitude * baseLifetime

scaledGapLifetimeProduct : ℚ → ℚ → ℚ → ℚ → ℚ
scaledGapLifetimeProduct inverseAmplitude amplitude baseGap baseLifetime =
  rescaledGap inverseAmplitude baseGap
  * rescaledBackwardLifetime amplitude baseLifetime

squareInverseProduct :
  (inverseAmplitude amplitude : ℚ) →
  inverseAmplitude * amplitude ≡ 1ℚ →
  square inverseAmplitude * square amplitude ≡ 1ℚ
squareInverseProduct inverseAmplitude amplitude inverse =
  trans
    (solve (inverseAmplitude ∷ amplitude ∷ []))
    (cong square inverse)

spectralGapBackwardLifetimeScaleInvariant :
  (inverseAmplitude amplitude baseGap baseLifetime : ℚ) →
  inverseAmplitude * amplitude ≡ 1ℚ →
  scaledGapLifetimeProduct
      inverseAmplitude amplitude baseGap baseLifetime
  ≡ baseGap * baseLifetime
spectralGapBackwardLifetimeScaleInvariant
    inverseAmplitude amplitude baseGap baseLifetime inverse =
  let
    regroup :
      scaledGapLifetimeProduct
          inverseAmplitude amplitude baseGap baseLifetime
      ≡ (square inverseAmplitude * square amplitude)
        * (baseGap * baseLifetime)
    regroup =
      solve (inverseAmplitude ∷ amplitude ∷ baseGap ∷ baseLifetime ∷ [])

    inverseSquares : square inverseAmplitude * square amplitude ≡ 1ℚ
    inverseSquares = squareInverseProduct inverseAmplitude amplitude inverse
  in
  trans regroup
    (trans
      (cong (_* (baseGap * baseLifetime)) inverseSquares)
      (solve (baseGap ∷ baseLifetime ∷ [])))

-- The result is intentionally coefficient-agnostic: baseGap may include the
-- physical viscosity and the exact first periodic eigenvalue (e.g. the usual
-- 4*pi^2/L^2 factor).  Whatever fixed coefficient is present, blow-up scaling
-- does not amplify its total backward damping exponent.
