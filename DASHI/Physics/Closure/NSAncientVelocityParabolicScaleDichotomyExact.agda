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
-- Let M be the velocity amplitude at time t and tau = T-t the remaining
-- physical time to a putative first singularity.  With r_v = 1/M and
-- alpha = M^2 tau, the exact squared-scale identity is
--
--   tau = alpha r_v^2.
--
-- Thus the parabolic radius sqrt(tau) is sqrt(alpha) velocity radii.  CKN
-- non-smallness at singular parabolic scales does not automatically descend
-- to r_v.  Bounded alpha is the L-infinity Type-I scale regime; alpha growing
-- large is precisely Type-II scale separation.
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

velocityScaleInverseMeaning :
  (amplitude inverseAmplitude : ℚ) →
  inverseAmplitude * amplitude ≡ 1ℚ →
  velocityScaleSquared inverseAmplitude * square amplitude ≡ 1ℚ
velocityScaleInverseMeaning amplitude inverseAmplitude inverse =
  trans
    (solve (inverseAmplitude ∷ amplitude ∷ []))
    (cong square inverse)

parabolicScaleIsAlphaTimesVelocityScaleSquared :
  (amplitude inverseAmplitude timeToSingularity : ℚ) →
  inverseAmplitude * amplitude ≡ 1ℚ →
  parabolicScaleSquared timeToSingularity
  ≡ normalizedForwardSingularityTime amplitude timeToSingularity
    * velocityScaleSquared inverseAmplitude
parabolicScaleIsAlphaTimesVelocityScaleSquared
    amplitude inverseAmplitude timeToSingularity inverse =
  let
    regroup :
      normalizedForwardSingularityTime amplitude timeToSingularity
        * velocityScaleSquared inverseAmplitude
      ≡ timeToSingularity
        * (velocityScaleSquared inverseAmplitude * square amplitude)
    regroup = solve (amplitude ∷ inverseAmplitude ∷ timeToSingularity ∷ [])

    inverseSquared :
      velocityScaleSquared inverseAmplitude * square amplitude ≡ 1ℚ
    inverseSquared = velocityScaleInverseMeaning amplitude inverseAmplitude inverse
  in
  trans
    (solve (timeToSingularity ∷ []))
    (trans
      (cong (timeToSingularity *_) (sym inverseSquared))
      (sym regroup))
  where
    open import Relation.Binary.PropositionalEquality using (sym)

normalizedForwardTimeIsSquaredScaleMismatch :
  (amplitude inverseAmplitude timeToSingularity : ℚ) →
  inverseAmplitude * amplitude ≡ 1ℚ →
  normalizedForwardSingularityTime amplitude timeToSingularity
    * velocityScaleSquared inverseAmplitude
  ≡ parabolicScaleSquared timeToSingularity
normalizedForwardTimeIsSquaredScaleMismatch
    amplitude inverseAmplitude timeToSingularity inverse =
  sym
    (parabolicScaleIsAlphaTimesVelocityScaleSquared
      amplitude inverseAmplitude timeToSingularity inverse)
  where
    open import Relation.Binary.PropositionalEquality using (sym)
