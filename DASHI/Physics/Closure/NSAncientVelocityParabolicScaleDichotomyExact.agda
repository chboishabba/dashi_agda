module DASHI.Physics.Closure.NSAncientVelocityParabolicScaleDichotomyExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Authors: Luis Caffarelli; Robert Kohn; Louis Nirenberg.
-- Title: "Partial regularity of suitable weak solutions of the
--         Navier-Stokes equations".
-- DOI: 10.1002/cpa.3160350604.
--
-- Authors: Tobias Barker; Christophe Prange.
-- Title: "Quantitative Regularity for the Navier-Stokes Equations Via
--         Spatial Concentration".
-- DOI: 10.1007/s00220-021-04122-x.
--
-- ROUND65 / EXACT SCALE-MATCHING PARAMETER
--
-- Let M be the velocity amplitude at time t and let tau = T-t be the
-- remaining physical time to a putative first singularity.  There are two
-- natural spatial scales:
--
--   velocity scale   r_v = 1/M,
--   parabolic scale  r_p = sqrt(tau).
--
-- Their squared ratio is exactly
--
--   (r_p / r_v)^2 = M^2 tau =: alpha.
--
-- Hence CKN non-smallness at singular parabolic scales does not by itself
-- imply non-smallness at the KNSŠ velocity scale.  The missing transfer is
-- precisely control across alpha.  Bounded alpha is the L-infinity Type-I
-- scaling regime; alpha -> infinity is the Type-II scale-separation regime.
--
-- This file proves only the algebraic seam and deliberately avoids a square
-- root carrier by working with squared scales.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

square : ℚ → ℚ
square x = x * x

velocityScaleSquared : ℚ → ℚ
velocityScaleSquared inverseAmplitude = square inverseAmplitude

parabolicScaleSquared : ℚ → ℚ
parabolicScaleSquared timeToSingularity = timeToSingularity

normalizedForwardSingularityTime : ℚ → ℚ → ℚ
normalizedForwardSingularityTime amplitude timeToSingularity =
  square amplitude * timeToSingularity

scaleRatioSquaredWithoutDivision : ℚ → ℚ → ℚ → ℚ
scaleRatioSquaredWithoutDivision
    amplitude inverseAmplitude timeToSingularity =
  parabolicScaleSquared timeToSingularity
  * square amplitude

velocityScaleInverseMeaning :
  (amplitude inverseAmplitude : ℚ) →
  inverseAmplitude * amplitude ≡ 1ℚ →
  velocityScaleSquared inverseAmplitude * square amplitude ≡ 1ℚ
velocityScaleInverseMeaning amplitude inverseAmplitude inverse =
  trans
    (solve (inverseAmplitude ∷ amplitude ∷ []))
    (cong square inverse)

scaleMismatchIsNormalizedForwardTime :
  (amplitude inverseAmplitude timeToSingularity : ℚ) →
  inverseAmplitude * amplitude ≡ 1ℚ →
  scaleRatioSquaredWithoutDivision
      amplitude inverseAmplitude timeToSingularity
  ≡ normalizedForwardSingularityTime amplitude timeToSingularity
scaleMismatchIsNormalizedForwardTime
    amplitude inverseAmplitude timeToSingularity inverse =
  solve (amplitude ∷ inverseAmplitude ∷ timeToSingularity ∷ [])

-- In KNSŠ coordinates s = M^2 (t-T_selected), the physical first singular
-- time T sits alpha = M^2 (T-t_selected) units to the future.  The same alpha
-- is therefore simultaneously the forward-time distance and squared spatial
-- scale mismatch between sqrt(T-t) and 1/M.
forwardTimeAndScaleMismatchAreSameParameter :
  (amplitude inverseAmplitude timeToSingularity : ℚ) →
  inverseAmplitude * amplitude ≡ 1ℚ →
  scaleRatioSquaredWithoutDivision
      amplitude inverseAmplitude timeToSingularity
  ≡ normalizedForwardSingularityTime amplitude timeToSingularity
forwardTimeAndScaleMismatchAreSameParameter =
  scaleMismatchIsNormalizedForwardTime
