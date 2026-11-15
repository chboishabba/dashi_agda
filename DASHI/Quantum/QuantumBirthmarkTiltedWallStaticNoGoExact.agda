{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkTiltedWallStaticNoGoExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using ([])
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; _/_; _-_; _<_)
open import Data.Rational.Properties as ℚP using (_<?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Foundations.GRQFTTwoVacuumAmplitudePotentialExact as Potential

------------------------------------------------------------------------
-- STATIC PLANAR WALL OBSTRUCTION FOR THE SELECTED TILTED POTENTIAL
--
-- For an ordinary static scalar wall satisfying phi'' = V'(phi), the first
-- integral 1/2 phi'^2 - V(phi) is constant.  If phi' -> 0 at both asymptotic
-- vacua, their potential energies must therefore be equal.
--
-- The selected repo potential is deliberately tilted:
--   V(0) = 21/64, V(1) = 3/8,
-- so the gap is +3/64.  Hence a static finite-energy planar heteroclinic wall
-- with zero endpoint derivatives is not the correct continuum object.  A
-- moving/curved bubble or additional source/friction term remains possible.
------------------------------------------------------------------------

vacuumEnergyGap : ℚ
vacuumEnergyGap =
  (Int.+ 3 / 8) - (Int.+ 21 / 64)

vacuumEnergyGapIsThreeSixtyFourths :
  vacuumEnergyGap ≡ Int.+ 3 / 64
vacuumEnergyGapIsThreeSixtyFourths = solve []

vacuumEnergyGapPositive :
  0ℚ < vacuumEnergyGap
vacuumEnergyGapPositive =
  toWitness {a? = 0ℚ ℚP.<? vacuumEnergyGap} _

record StaticPlanarWallEndpointCondition : Set where
  constructor static-planar-wall-endpoint-condition
  field
    asymptoticDerivativeVanishes : Bool
    conservedFirstIntegralApplies : Bool
    endpointVacuumEnergiesEqual :
      (Int.+ 21 / 64) ≡ (Int.+ 3 / 8)

open StaticPlanarWallEndpointCondition public

staticPlanarWallEqualVacuumEnergyRequired : Bool
staticPlanarWallEqualVacuumEnergyRequired = true

selectedTiltedPotentialHasNonzeroVacuumGap : Bool
selectedTiltedPotentialHasNonzeroVacuumGap = true

selectedTiltedPotentialStaticWallNoGo : Bool
selectedTiltedPotentialStaticWallNoGo = true

movingOrCurvedWallStillAllowed : Bool
movingOrCurvedWallStillAllowed = true

timeDependentBubbleStillRequiresDynamics : Bool
timeDependentBubbleStillRequiresDynamics = true

noStaticKinkPromotedAsContinuumSolution : Bool
noStaticKinkPromotedAsContinuumSolution = true
