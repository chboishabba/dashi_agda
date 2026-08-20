module DASHI.Physics.Closure.NSTriadKNQuadraticCubicNormalFormCoercivityNoGoExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- DASHI MAKE-OR-BREAK HOMOGENEITY NO-GO
--
-- The global Round106/normal-form escape has corrected energy
--
--      Y(u) = nu X(u) + G(u),
--
-- where X is quadratic in velocity and G=sum g_tau A_tau is cubic.  Round104
-- already proves that the Waleffe phase amplitude changes sign at fixed radii
-- and helicity signs.  Therefore a quadratic-plus-cubic functional cannot be
-- globally coercive on an amplitude-closed arbitrary-data class merely from
-- positivity of nu and X: a negative cubic direction eventually dominates
-- under u -> a u.
--
-- This file gives the exact rational witness
--
--      nu = 1, X_base = 1, G_base = -1, a = 2,
--
-- so
--
--      Y(a u) = a^2 - a^3 = 4 - 8 = -4 < 0.
--
-- It also connects the negative cubic direction to the repository's literal
-- 3-4-5 Waleffe sign-flip witness: the fixed-geometry negative cell has
-- amplitude exactly -1.
--
-- The theorem does NOT say that every possible higher-order normal form is
-- impossible.  It says the simple corrected critical energy from the exact
-- phase integration cannot itself be the arbitrary-data coercive Lyapunov
-- quantity unless an additional physical theorem forces the COMPLETE cubic
-- correction to have a favourable sign/cancellation.  Adding such a theorem
-- would be new mathematics, not free algebra.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open ℚP using (_<?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Relation.Nullary.Negation.Core using (¬_)

import DASHI.Physics.Closure.NSTriadKNHeterochiralMinorityLegReductionRound102Exact as W
import DASHI.Physics.Closure.NSTriadKNWaleffeLeithPointwiseMobilityNoGoRound104Exact as R104

square cube : ℚ → ℚ
square a = a * a
cube a = (a * a) * a

scaledQuadraticCubicCorrection :
  (viscosity baseQuadratic baseCubic amplitudeScale : ℚ) → ℚ
scaledQuadraticCubicCorrection viscosity baseQuadratic baseCubic amplitudeScale =
  viscosity * square amplitudeScale * baseQuadratic
  + cube amplitudeScale * baseCubic

one two four : ℚ
one = 1ℚ
two = Int.+ 2 / 1
four = Int.+ 4 / 1

negativeCubicWitness : ℚ
negativeCubicWitness = - one

literalThreeFourFiveNegativeAmplitude :
  W.amplitude R104.threeFourFiveNegativeCell ≡ negativeCubicWitness
literalThreeFourFiveNegativeAmplitude = refl

witnessCorrectedEnergyIsMinusFour :
  scaledQuadraticCubicCorrection one one negativeCubicWitness two ≡ - four
witnessCorrectedEnergyIsMinusFour = solve []

minusFourStrictlyNegative : - four < 0ℚ
minusFourStrictlyNegative = toWitness {a? = (- four) <? 0ℚ} _

witnessCorrectedEnergyStrictlyNegative :
  scaledQuadraticCubicCorrection one one negativeCubicWitness two < 0ℚ
witnessCorrectedEnergyStrictlyNegative
  rewrite witnessCorrectedEnergyIsMinusFour = minusFourStrictlyNegative

witnessRefutesGlobalNonnegativeCoercivity :
  ¬ (0ℚ ≤ scaledQuadraticCubicCorrection one one negativeCubicWitness two)
witnessRefutesGlobalNonnegativeCoercivity proposed =
  ℚP.<-irrefl 0ℚ
    (ℚP.<-≤-trans witnessCorrectedEnergyStrictlyNegative proposed)

quadraticCubicScalingMeaning :
  (nu X G a : ℚ) →
  scaledQuadraticCubicCorrection nu X G a
  ≡ (nu * X) * (a * a) + G * ((a * a) * a)
quadraticCubicScalingMeaning nu X G a = solve (nu ∷ X ∷ G ∷ a ∷ [])

simpleGlobalPhaseNormalFormIsAutomaticallyCoercive : Bool
simpleGlobalPhaseNormalFormIsAutomaticallyCoercive = false

literalWaleffeNegativeCubicDirectionExists : Bool
literalWaleffeNegativeCubicDirectionExists = true

negativeCubicDirectionCreatesLargeAmplitudeCoercivityObstruction : Bool
negativeCubicDirectionCreatesLargeAmplitudeCoercivityObstruction = true

simpleGlobalPhaseNormalFormIsAutomaticallyCoerciveIsFalse :
  simpleGlobalPhaseNormalFormIsAutomaticallyCoercive ≡ false
simpleGlobalPhaseNormalFormIsAutomaticallyCoerciveIsFalse = refl

literalWaleffeNegativeCubicDirectionExistsIsTrue :
  literalWaleffeNegativeCubicDirectionExists ≡ true
literalWaleffeNegativeCubicDirectionExistsIsTrue = refl

negativeCubicDirectionCreatesLargeAmplitudeCoercivityObstructionIsTrue :
  negativeCubicDirectionCreatesLargeAmplitudeCoercivityObstruction ≡ true
negativeCubicDirectionCreatesLargeAmplitudeCoercivityObstructionIsTrue = refl
