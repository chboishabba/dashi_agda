module DASHI.Physics.Closure.NSTriadKNLuoEnergyInterpolationDeficitExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Joran Bergh; Jorgen Lofstrom.
-- Title: "Interpolation Spaces: An Introduction".
-- Springer, 1976.
-- DOI: 10.1007/978-3-642-66451-9.
--
-- Author: James Serrin.
-- Title: "On the Interior Regularity of Weak Solutions of the
-- Navier--Stokes Equations".
-- Archive for Rational Mechanics and Analysis 9 (1962), 187--195.
-- DOI: 10.1007/BF00253344.
--
-- PURPOSE
-- Prove exactly that interpolation between the energy endpoints
--
--   L_t^infinity L_x^2  and  L_t^2 L_x^6
--
-- stays on 2/r + 3/s = 3/2.  The critical Serrin line is 1, so ordinary
-- interpolation preserves a deficit of exactly 1/2 and cannot manufacture
-- the missing half derivative.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

two three six : ℚ
two = Int.+ 2 / 1
three = Int.+ 3 / 1
six = Int.+ 6 / 1

inverseTimeExponent : ℚ → ℚ
inverseTimeExponent theta = theta * (Int.+ 1 / 2)

inverseSpaceExponent : ℚ → ℚ
inverseSpaceExponent theta =
  (Int.+ 1 / 1 - theta) * (Int.+ 1 / 2)
  + theta * (Int.+ 1 / 6)

energyInterpolationIndex : ℚ → ℚ
energyInterpolationIndex theta =
  two * inverseTimeExponent theta
  + three * inverseSpaceExponent theta

energyInterpolationAlwaysThreeHalves :
  (theta : ℚ) →
  energyInterpolationIndex theta ≡ Int.+ 3 / 2
energyInterpolationAlwaysThreeHalves theta = solve (theta ∷ [])

serrinCriticalIndex : ℚ
serrinCriticalIndex = Int.+ 1 / 1

energyInterpolationDeficit : ℚ → ℚ
energyInterpolationDeficit theta =
  energyInterpolationIndex theta - serrinCriticalIndex

energyInterpolationDeficitIsOneHalf :
  (theta : ℚ) →
  energyInterpolationDeficit theta ≡ Int.+ 1 / 2
energyInterpolationDeficitIsOneHalf theta = solve (theta ∷ [])
