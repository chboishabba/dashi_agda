module DASHI.Physics.Closure.NSTriadKNLuoNearWindowCriticalGainExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
--
-- Authors: Peter Constantin; Charles Fefferman; Andrew J. Majda.
-- Title: "Geometric Constraints on Potentially Singular Solutions for the
-- 3-D Euler Equations".
-- Communications in Partial Differential Equations 21 (1996), 559--571.
-- DOI: 10.1080/03605309608821197.
--
-- PURPOSE
-- The round-seven no-go proves that the energy-only newest-layer model is
-- exactly 2 lambda_q.  This module computes, rather than merely names, the
-- missing scale-sensitive gain.  The factor
--
--   gamma_q = 1 / (128 lambda_q)
--
-- turns the obstruction into the desired half-budget:
--
--   (2 lambda_q) gamma_q = 1/64.
--
-- The corrected Fourier strain theorem proves exact cancellation of the
-- diagonal single-mode stretching contribution.  Consequently the required
-- gamma_q must be paid by the off-diagonal/cross-mode coherence defect.  No
-- unconditional estimate of that defect is asserted here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteEnergyCriticalScalingGapExact as Scale
import DASHI.Physics.Closure.NSTriadKNLuoFiniteNearWindowHalfKernelExact as Near
import DASHI.Physics.Closure.NSTriadKNLuoFiniteNearWindowScalingObstructionExact as Obstruction

oneHundredTwentyEighth : ℚ
oneHundredTwentyEighth = Int.+ 1 / 128

oneSixtyFourth : ℚ
oneSixtyFourth = Int.+ 1 / 64

requiredCrossModeGain : Nat → ℚ
requiredCrossModeGain shell =
  oneHundredTwentyEighth * Near.windowRoot shell

gainMeaning :
  (shell : Nat) →
  requiredCrossModeGain shell
  ≡ oneHundredTwentyEighth / Scale.dyadicScale shell
gainMeaning shell =
  solve
    ( Near.windowRoot shell
    ∷ Scale.dyadicScale shell
    ∷ [])

requiredGainClosesNearHalfBudget :
  (shell : Nat) →
  Obstruction.nearEnergyOnlyModel shell
    * requiredCrossModeGain shell
  ≡ oneSixtyFourth
requiredGainClosesNearHalfBudget shell =
  trans
    (congProduct shell)
    (trans
      (solve
        ( Near.windowRoot shell
        ∷ Scale.dyadicScale shell
        ∷ []
        ))
      (substituteReciprocal shell))
  where
  congProduct :
    (shell : Nat) →
    Obstruction.nearEnergyOnlyModel shell
      * requiredCrossModeGain shell
    ≡ (Scale.two * Scale.dyadicScale shell)
      * (oneHundredTwentyEighth * Near.windowRoot shell)
  congProduct shell
    rewrite Obstruction.nearEnergyOnlyMeaning shell =
    solve
      ( Scale.dyadicScale shell
      ∷ Near.windowRoot shell
      ∷ [])

  substituteReciprocal :
    (shell : Nat) →
    (Int.+ 1 / 64)
      * (Near.windowRoot shell * Scale.dyadicScale shell)
    ≡ oneSixtyFourth
  substituteReciprocal shell
    rewrite Obstruction.reciprocalDyadicIdentity shell =
    solve []

physicalNearGainCloses :
  (shell : Nat) →
  (physicalNear : ℚ) →
  physicalNear
    ≤ Obstruction.nearEnergyOnlyModel shell
      * requiredCrossModeGain shell →
  physicalNear ≤ oneSixtyFourth
physicalNearGainCloses shell physicalNear physicalBound =
  subst
    (λ upper → physicalNear ≤ upper)
    (requiredGainClosesNearHalfBudget shell)
    physicalBound
