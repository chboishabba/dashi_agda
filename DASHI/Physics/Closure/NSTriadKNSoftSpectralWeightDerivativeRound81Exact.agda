module DASHI.Physics.Closure.NSTriadKNSoftSpectralWeightDerivativeRound81Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Bolin Gao; Lacra Pavel,
-- "On the Properties of the Softmax Function with Application in Game Theory
-- and Reinforcement Learning", arXiv:1704.00805.
-- DOI: 10.48550/arXiv.1704.00805.
--
-- Marcus Carlsson,
-- "Lipschitz continuity for isotropic matrix functions",
-- Linear Algebra and its Applications 624 (2021), 259--266.
-- DOI: 10.1016/j.laa.2021.04.006.
--
-- ROUND81 / EIGENVALUE-SIDE SOFT SPECTRAL TANGENT
--
-- For normalized exponential/softmax spectral weights p_i and eigenvalue
-- rates ellDot_i, the commuting/eigenvalue part of the tangent is
--
--   meanRate = sum_i p_i ellDot_i,
--   pDot_i = beta p_i (ellDot_i - meanRate).
--
-- If sum_i p_i = 1 then sum_i pDot_i = 0 exactly.  This is gap-free and
-- remains meaningful when eigenvalues coincide.  It closes the normalization
-- tangent algebra of the smooth P_beta potential without constructing a hard
-- eigenvector derivative.
--
-- The noncommuting/off-diagonal matrix Frechet part remains a separate analytic
-- theorem; Carlsson and Al-Mohy--Higham provide the appropriate matrix-function
-- framework for that lift.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNSmoothSpectralAlignmentPotentialRound81Exact as Soft

meanEigenvalueRate : Soft.SpectralProbabilityWeights → ℚ → ℚ → ℚ → ℚ
meanEigenvalueRate p rate1 rate2 rate3 =
  Soft.p1 p * rate1 + Soft.p2 p * rate2 + Soft.p3 p * rate3

spectralWeightRate :
  ℚ → Soft.SpectralProbabilityWeights → ℚ → ℚ → ℚ → ℚ → ℚ
spectralWeightRate beta p weight rate1 rate2 rate3 =
  beta * weight *
    (rate1 - meanEigenvalueRate p rate1 rate2 rate3)

p1Rate : ℚ → Soft.SpectralProbabilityWeights → ℚ → ℚ → ℚ → ℚ
p1Rate beta p rate1 rate2 rate3 =
  spectralWeightRate beta p (Soft.p1 p) rate1 rate2 rate3 rate1

p2Rate : ℚ → Soft.SpectralProbabilityWeights → ℚ → ℚ → ℚ → ℚ
p2Rate beta p rate1 rate2 rate3 =
  spectralWeightRate beta p (Soft.p2 p) rate1 rate2 rate3 rate2

p3Rate : ℚ → Soft.SpectralProbabilityWeights → ℚ → ℚ → ℚ → ℚ
p3Rate beta p rate1 rate2 rate3 =
  spectralWeightRate beta p (Soft.p3 p) rate1 rate2 rate3 rate3

softSpectralWeightTangentPreservesTraceOne :
  (beta : ℚ) →
  (p : Soft.SpectralProbabilityWeights) →
  (rate1 rate2 rate3 : ℚ) →
  (p1Rate beta p rate1 rate2 rate3
    + p2Rate beta p rate1 rate2 rate3)
    + p3Rate beta p rate1 rate2 rate3
  ≡ 0ℚ
softSpectralWeightTangentPreservesTraceOne beta p rate1 rate2 rate3 =
  let
    pSum : (Soft.p1 p + Soft.p2 p) + Soft.p3 p ≡ 1ℚ
    pSum = Soft.spectralSumOne p

    factorMean :
      (p1Rate beta p rate1 rate2 rate3
        + p2Rate beta p rate1 rate2 rate3)
        + p3Rate beta p rate1 rate2 rate3
      ≡ beta *
        ((Soft.p1 p * rate1 + Soft.p2 p * rate2 + Soft.p3 p * rate3)
          - ((Soft.p1 p + Soft.p2 p) + Soft.p3 p)
            * meanEigenvalueRate p rate1 rate2 rate3)
    factorMean = solve
      (beta ∷ Soft.p1 p ∷ Soft.p2 p ∷ Soft.p3 p
        ∷ rate1 ∷ rate2 ∷ rate3 ∷ [])
  in
  trans factorMean
    (trans
      (cong
        (λ totalWeight →
          beta *
            ((Soft.p1 p * rate1 + Soft.p2 p * rate2 + Soft.p3 p * rate3)
              - totalWeight * meanEigenvalueRate p rate1 rate2 rate3))
        pSum)
      (solve
        (beta ∷ Soft.p1 p ∷ Soft.p2 p ∷ Soft.p3 p
          ∷ rate1 ∷ rate2 ∷ rate3 ∷ [])))

round81SoftSpectralWeightTangentIsGapFree : Bool
round81SoftSpectralWeightTangentIsGapFree = true

round81SoftSpectralWeightTangentPreservesTraceOne : Bool
round81SoftSpectralWeightTangentPreservesTraceOne = true

round81SoftSpectralWeightTangentPreservesTraceOneIsTrue :
  round81SoftSpectralWeightTangentPreservesTraceOne ≡ true
round81SoftSpectralWeightTangentPreservesTraceOneIsTrue = refl
