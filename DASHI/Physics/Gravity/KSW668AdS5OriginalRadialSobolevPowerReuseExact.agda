module DASHI.Physics.Gravity.KSW668AdS5OriginalRadialSobolevPowerReuseExact where

------------------------------------------------------------------------
-- KSW IX: reusable ALL-NATURAL-ORDER commutation theorem.
--
-- In original a=t moving AdS5 tensor F8, A=-L_r is the EXACT
-- conservative radial finite-volume stiffness (effective d=3,7,11).
-- The T-dependent coefficients b,v, AdS 3/z, normal SBP2 and weak
-- original Israel SAT act in T,y independently of radial r.
-- The separate physical finite-matrix proof obligation is
--     A (FullMovingStage X) = FullMovingStage (A X)
-- when the prescribed original TT source is transformed in parallel.
--
-- This module rigorously proves the general induction from one
-- commuting operator to EVERY natural radial power, without
-- postulating a concrete five-dimensional physical tensor action.
-- Source-level proof only; pinned Agda 2.9 kernel unrun.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

module _
  {State : Set}
  (radial : State → State)
  (coupledStage : State → State)
  (commuteRadialStage : (x : State) →
    radial (coupledStage x) ≡ coupledStage (radial x))
  where

  radialPower : Nat → State → State
  radialPower zero x = x
  radialPower (suc n) x = radial (radialPower n x)

  originalAllRadialSobolevPowersCommute :
    (n : Nat) (x : State) →
    radialPower n (coupledStage x)
      ≡ coupledStage (radialPower n x)
  originalAllRadialSobolevPowersCommute zero x = refl
  originalAllRadialSobolevPowersCommute (suc n) x =
    trans
      (cong radial (originalAllRadialSobolevPowersCommute n x))
      (commuteRadialStage (radialPower n x))

-- What remains OPEN: actual 5D differential/infinite-dimensional
-- Sobolev completion, uniform-in-grid source H^(4+epsilon),
-- both Weyl boundary trace, coupled fully discrete SSPRK3 stability,
-- original t2 FIO acceptance, matter action and empirical observation.
