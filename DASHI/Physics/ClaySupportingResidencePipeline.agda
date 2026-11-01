module DASHI.Physics.ClaySupportingResidencePipeline where

open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties
  using ( ≤-refl; ≤-trans; *-mono-≤ )
open import DASHI.Physics.ClaySupportingResidenceTimeAlgebra
  using (residenceAlgebraLemma)

----------------------------------------------------------------------
-- Step A: integrated danger N² bound from integrated residue N² bound
--
--   Danger_N ≤ Residue_N      (pointwise, per shell N)
--   N² * Residue_N ≤ C        (integrated residue bound)
--   ⇒ N² * Danger_N ≤ C
--
-- This is monotonicity + transitivity.  It is not a receipt — it
-- consumes the real integrated-residue theorem.
----------------------------------------------------------------------

integratedDangerFromResidue :
  (N2 danger residue C : Nat) →
  danger ≤ residue →
  N2 * residue ≤ C →
  N2 * danger ≤ C
integratedDangerFromResidue N2 danger residue C danger≤residue residueBound =
  let
    step : N2 * danger ≤ N2 * residue
    step = *-mono-≤ (≤-refl {N2}) danger≤residue
  in
  ≤-trans step residueBound

----------------------------------------------------------------------
-- Step B: residence-time exclusion from integrated residue bound
--
--   λ * |E_N(λ)| ≤ Danger_N          (Markov / Chebyshev)
--   Danger_N ≤ Residue_N             (danger dominated by residue)
--   N² * Residue_N ≤ C               (integrated residue N² bound)
--   ⇒ |E_N(λ)| * (λ * N²) ≤ C
--
-- The proof chains:
--   1. N² * Danger_N  ≤  N² * Residue_N ≤ C    (Step A)
--   2. residenceAlgebraLemma gives final form
----------------------------------------------------------------------

residenceFromIntegratedResidue :
  (measureE lambda N2 C : Nat) →
  (danger residue : Nat) →
  lambda * measureE ≤ danger →
  danger ≤ residue →
  N2 * residue ≤ C →
  measureE * (lambda * N2) ≤ C
residenceFromIntegratedResidue measureE lambda N2 C danger residue
  markovBound danger≤residue residueBound =
  let
    dangerBound : N2 * danger ≤ C
    dangerBound = integratedDangerFromResidue N2 danger residue C
                    danger≤residue residueBound
  in
  residenceAlgebraLemma measureE lambda N2 C danger markovBound dangerBound
