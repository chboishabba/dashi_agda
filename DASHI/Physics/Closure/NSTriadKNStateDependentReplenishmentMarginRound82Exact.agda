module DASHI.Physics.Closure.NSTriadKNStateDependentReplenishmentMarginRound82Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CALIBRATION
--
-- Sean P. Meyn; Richard L. Tweedie,
-- "Markov Chains and Stochastic Stability", 2nd ed., Cambridge University
-- Press, 2009. DOI: 10.1017/CBO9780511626630.
--
-- Pekka Tuominen; Richard L. Tweedie,
-- "Subgeometric rates of convergence of f-ergodic Markov chains",
-- Advances in Applied Probability 26 (1994), 775--798.
-- DOI: 10.2307/1427445.
--
-- Roger Temam,
-- "Infinite-Dimensional Dynamical Systems in Mechanics and Physics", 2nd ed.,
-- Springer, 1997. DOI: 10.1007/978-1-4612-0645-3.
--
-- AUTHORITY BOUNDARY
--
-- The stochastic sources calibrate why state-dependent/subgeometric drift
-- conditions are natural fallbacks when one uniform contraction factor is too
-- strong.  No Markov-chain theorem is imported below.  The exact deterministic
-- fact is already present in DASHI's compact-Gamma absorption algebra.
--
-- ROUND82 / NO UNIFORM THETA REQUIRED
--
-- The common shorthand
--
--   R <= theta E + C, theta < 1,
--
-- is sufficient but not the actual theorem interface.  The existing core asks
-- only for an additive split
--
--   E = M + A,
--   R <= A + C,
--
-- where M is the retained escape margin and A is the part consumed by
-- replenishment.  Then
--
--   M <= initialPotential + C.
--
-- Hence the physical C5 producer may choose A state-by-state or interval-by-
-- interval.  It need not manufacture one global scalar theta, provided it can
-- still construct a positive occupation-paying margin M uniformly enough for
-- the final cutoff family.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption as Absorb

stateDependentAbsorptionStillBoundsMargin :
  (A : Absorb.AbsorptionArithmetic) →
  (I : Absorb.CompactGammaAbsorptionInputs A) →
  Absorb._≤_ A
    (Absorb.marginEscape I)
    (Absorb._+_ A
      (Absorb.initialPotential I)
      (Absorb.remainderConstant I))
stateDependentAbsorptionStillBoundsMargin =
  Absorb.absorbedReplenishmentBoundsEscapeMargin

round82UniformScalarThetaRequiredByAbsorptionCore : Bool
round82UniformScalarThetaRequiredByAbsorptionCore = false

round82StateDependentAbsorbedPartSupportedByExistingCore : Bool
round82StateDependentAbsorbedPartSupportedByExistingCore = true

round82StateDependentAbsorbedPartSupportedByExistingCoreIsTrue :
  round82StateDependentAbsorbedPartSupportedByExistingCore ≡ true
round82StateDependentAbsorbedPartSupportedByExistingCoreIsTrue = refl
