module DASHI.Physics.Closure.NSTriadKNLuoFiniteNearWindowScalingObstructionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Darko Mitrović.
-- Title: "A High-Frequency Tail Condition and a Diagnostic Iteration for
-- the Navier--Stokes Equations".
-- arXiv:2411.02568.
-- DOI: none assigned in the cited preprint version.
--
-- Authors: Diego Córdoba; Luis Martínez-Zoroa; Fan Zheng.
-- Title: "Finite Time Blow-Up for the Hypodissipative Navier Stokes
-- Equations with a Force in L^1_t C_x^{1,epsilon} cap L^infinity_t L^2_x".
-- Archive for Rational Mechanics and Analysis 250 (2026), article 38.
-- DOI: 10.1007/s00205-026-02198-0.
--
-- PURPOSE
-- Prove the exact scaling obstruction in the newest parabolic layer.  On the
-- standard q-th dyadic window,
--
--   half-kernel mass = 2 lambda_q^{-1},
--   two-derivative curvature cost = lambda_q^2.
--
-- Their product is therefore
--
--   2 lambda_q,
--
-- despite unit shell energy.  It doubles at every shell and is already much
-- larger than 1/64 at q=0.  Thus energy plus the half-kernel time factor alone
-- cannot imply the near-window smallness theorem.  An additional spatial
-- moment, commutator, alignment or physical depletion estimate is necessary.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality as Eq
  using (cong; sym; trans)
open Eq.≡-Reasoning
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteEnergyCriticalScalingGapExact as Scale
import DASHI.Physics.Closure.NSTriadKNLuoFiniteNearWindowHalfKernelExact as Near
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

reciprocalDyadicIdentity :
  (shell : Nat) →
  Near.windowRoot shell * Scale.dyadicScale shell ≡ 1ℚ
reciprocalDyadicIdentity zero = refl
reciprocalDyadicIdentity (suc shell)
  rewrite reciprocalDyadicIdentity shell =
  solve
    ( Near.half
    ∷ Scale.two
    ∷ Near.windowRoot shell
    ∷ Scale.dyadicScale shell
    ∷ []
    )

curvatureCost : Nat → ℚ
curvatureCost shell =
  L2.square (Scale.dyadicScale shell)

unitEnergy : Nat → ℚ
unitEnergy shell = 1ℚ

energyInvariant :
  (shell : Nat) →
  unitEnergy (suc shell) ≡ unitEnergy shell
energyInvariant shell = refl

nearEnergyOnlyModel : Nat → ℚ
nearEnergyOnlyModel shell =
  Near.halfKernelMass shell * curvatureCost shell * unitEnergy shell

nearEnergyOnlyMeaning :
  (shell : Nat) →
  nearEnergyOnlyModel shell ≡ Scale.two * Scale.dyadicScale shell
nearEnergyOnlyMeaning shell =
  begin
    Near.halfKernelMass shell * curvatureCost shell * unitEnergy shell
  ≡⟨ solve
       ( Near.windowRoot shell
       ∷ Scale.dyadicScale shell
       ∷ []
       ) ⟩
    Scale.two
      * (Near.windowRoot shell * Scale.dyadicScale shell)
      * Scale.dyadicScale shell
  ≡⟨ cong
       (λ reciprocal → Scale.two * reciprocal * Scale.dyadicScale shell)
       (reciprocalDyadicIdentity shell) ⟩
    Scale.two * 1ℚ * Scale.dyadicScale shell
  ≡⟨ solve (Scale.dyadicScale shell ∷ []) ⟩
    Scale.two * Scale.dyadicScale shell
  ∎

nearEnergyOnlyDoubles :
  (shell : Nat) →
  nearEnergyOnlyModel (suc shell)
  ≡ Scale.two * nearEnergyOnlyModel shell
nearEnergyOnlyDoubles shell =
  trans
    (nearEnergyOnlyMeaning (suc shell))
    (trans
      (cong (Scale.two *_)
        (Scale.dyadicScaleSuccessor shell))
      (cong (Scale.two *_)
        (Eq.sym (nearEnergyOnlyMeaning shell))))

oneSixtyFourth : ℚ
oneSixtyFourth = Int.+ 1 / 64

thresholdAlreadyFailsAtBase :
  oneSixtyFourth ≤ nearEnergyOnlyModel zero
thresholdAlreadyFailsAtBase =
  toWitness {a? = oneSixtyFourth ≤? nearEnergyOnlyModel zero} _
