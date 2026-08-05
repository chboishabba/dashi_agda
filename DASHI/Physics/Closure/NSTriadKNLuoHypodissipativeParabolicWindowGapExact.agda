module DASHI.Physics.Closure.NSTriadKNLuoHypodissipativeParabolicWindowGapExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Diego Córdoba; Luis Martínez-Zoroa; Fan Zheng.
-- Title: "Finite Time Blow-Up for the Hypodissipative Navier Stokes
-- Equations with a Force in L^1_t C_x^{1,epsilon} cap L^infinity_t L^2_x".
-- Archive for Rational Mechanics and Analysis 250 (2026), article 38.
-- DOI: 10.1007/s00205-026-02198-0.
-- arXiv DOI: 10.48550/arXiv.2407.06776.
--
-- PURPOSE
-- Quantify why the strength of dissipation matters on the newest parabolic
-- layer, while keeping the paper's convention explicit.  On the standard
-- window delta_q=lambda_q^{-2},
--
--   delta_q lambda_q^2 = 1
--
-- for the classical Laplacian |nabla|^2, whereas for the illustrative weaker
-- operator |nabla| one has
--
--   delta_q lambda_q = lambda_q^{-1}.
--
-- Thus standard heat damping remains order one on its natural window, while
-- the weaker exponent loses a full dyadic factor.  This is a scaling audit;
-- it neither reproduces the cited blow-up construction nor claims blow-up for
-- every alpha<2.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality as Eq using (cong)
open Eq.≡-Reasoning

import DASHI.Physics.Closure.NSTriadKNLuoFiniteEnergyCriticalScalingGapExact as Scale
import DASHI.Physics.Closure.NSTriadKNLuoFiniteNearWindowHalfKernelExact as Near
import DASHI.Physics.Closure.NSTriadKNLuoFiniteNearWindowScalingObstructionExact as Obstruction
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

standardDissipationWeight : Nat → ℚ
standardDissipationWeight shell =
  L2.square (Scale.dyadicScale shell)

weakerDissipationWeight : Nat → ℚ
weakerDissipationWeight shell =
  Scale.dyadicScale shell

standardWeightContainsOneMoreFrequency :
  (shell : Nat) →
  standardDissipationWeight shell
  ≡ Scale.dyadicScale shell * weakerDissipationWeight shell
standardWeightContainsOneMoreFrequency shell = refl

standardParabolicExponent : Nat → ℚ
standardParabolicExponent shell =
  Near.windowLength shell * standardDissipationWeight shell

weakerParabolicExponent : Nat → ℚ
weakerParabolicExponent shell =
  Near.windowLength shell * weakerDissipationWeight shell

standardParabolicExponentIsOne :
  (shell : Nat) →
  standardParabolicExponent shell ≡ 1ℚ
standardParabolicExponentIsOne shell =
  begin
    Near.windowLength shell * standardDissipationWeight shell
  ≡⟨ solve
       ( Near.windowRoot shell
       ∷ Scale.dyadicScale shell
       ∷ []
       ) ⟩
    (Near.windowRoot shell * Scale.dyadicScale shell)
      * (Near.windowRoot shell * Scale.dyadicScale shell)
  ≡⟨ cong
       (λ reciprocal → reciprocal * reciprocal)
       (Obstruction.reciprocalDyadicIdentity shell) ⟩
    1ℚ * 1ℚ
  ≡⟨ refl ⟩
    1ℚ
  ∎

weakerParabolicExponentIsInverseFrequency :
  (shell : Nat) →
  weakerParabolicExponent shell ≡ Near.windowRoot shell
weakerParabolicExponentIsInverseFrequency shell =
  begin
    Near.windowLength shell * weakerDissipationWeight shell
  ≡⟨ solve
       ( Near.windowRoot shell
       ∷ Scale.dyadicScale shell
       ∷ []
       ) ⟩
    Near.windowRoot shell
      * (Near.windowRoot shell * Scale.dyadicScale shell)
  ≡⟨ cong
       (Near.windowRoot shell *_)
       (Obstruction.reciprocalDyadicIdentity shell) ⟩
    Near.windowRoot shell * 1ℚ
  ≡⟨ solve (Near.windowRoot shell ∷ []) ⟩
    Near.windowRoot shell
  ∎
