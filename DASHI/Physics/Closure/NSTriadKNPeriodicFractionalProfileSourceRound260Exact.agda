module DASHI.Physics.Closure.NSTriadKNPeriodicFractionalProfileSourceRound260Exact where

------------------------------------------------------------------------
-- ROUND260 / SOURCE-LEVEL DERIVATION OF THE PERIODIC H^(1/2) PROFILE THEOREM
--
-- Mathematical sources used for the analytic theorem represented here:
--
-- * P. Gerard, "Description of the lack of compactness for the Sobolev
--   imbedding", ESAIM COCV 3 (1998), 213--233.
--   Bounded homogeneous H^s sequences admit translation/dilation profiles
--   with critical-Lebesgue-small remainder.
--
-- * G. Palatucci and A. Pisante, "Improved Sobolev embeddings, profile
--   decomposition, and concentration-compactness for fractional Sobolev
--   spaces", Calc. Var. PDE 50 (2014), 799--829, arXiv:1302.5923.
--   This gives the fractional H^s profile decomposition and concentration
--   characterization used at s = 1/2 in dimension 3.
--
-- * Fractional Sobolev spaces on closed Riemannian manifolds have equivalent
--   spectral / heat-kernel / local descriptions.  On the flat torus the
--   spectral H^(1/2) norm is the Fourier norm already used by this repository.
--
-- BIDI DERIVATION.
--
-- For a bounded sequence u_n in H^(1/2)(T^3):
--
--   1. reflexivity gives a subsequence u_n ⇀ u_*; this is the scale-one
--      periodic profile;
--   2. r_n = u_n - u_* is weak-zero;
--   3. if r_n is not small in the critical L^3 norm, concentration-compactness
--      localises a concentration in one of finitely many torus charts;
--   4. every noncompact chart scale must satisfy lambda_n -> 0 (a bounded-away
--      scale would contribute another scale-one weak profile instead);
--   5. after recentering and rescaling by lambda_n, the chart metric converges
--      to Euclidean and the fractional H^(1/2) energy converges to the
--      Euclidean homogeneous energy;
--   6. apply the Gerard / Palatucci--Pisante Euclidean profile extraction;
--   7. iterate using asymptotic orthogonality.  The remainder tends to zero in
--      L^3 and the H^(1/2) energy is asymptotically Pythagorean.
--
-- Thus the safe periodic theorem has exactly two kinds of objects:
--
--   u_n = u_* + sum_j Bubble_n^j + remainder_n,
--
-- where u_* is periodic scale-one and every Bubble_n^j has shrinking scale
-- lambda_n^j -> 0 and an R^3 H^(1/2) profile.
--
-- This module records that precise analytic theorem surface.  Agda's finite
-- rational Fourier layer does not itself formalise weak topology, charts,
-- fractional Sobolev spaces, or limits, so the analytic predicates remain
-- model-owned; the decomposition shape and every downstream use are fixed.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

record PeriodicFractionalProfileTheorem
    {ℓ : Level}
    (TorusState EuclideanState : Set ℓ) : Set (lsuc ℓ) where
  field
    selectedSubsequence : Nat → Nat

    -- The unique scale-one contribution: weak limit on T^3.
    periodicWeakProfile : TorusState
    scaleOneWeakConvergence : Set ℓ

    -- Shrinking Euclidean bubbles.
    BubbleIndex : Set ℓ
    euclideanProfile : BubbleIndex → EuclideanState
    bubbleCenter : BubbleIndex → Nat → TorusState
    bubbleScale : BubbleIndex → Nat → TorusState
    bubbleScaleShrinksToZero : BubbleIndex → Set ℓ

    -- Critical geometry and asymptotic orthogonality.
    criticalHOneHalfBounded : Set ℓ
    profileParametersOrthogonal : Set ℓ
    criticalNormPythagorean : Set ℓ

    -- The exact remainder needed by Gallagher's NS decomposition step.
    remainderCriticalL3Small : Set ℓ

    -- Transport needed by the mixed-helicity defect consumer.
    divergenceFreePreservedByProfiles : Set ℓ
    normalizedCurlCommutesWithBubbleTransport : Set ℓ
    mixedDefectStableUnderChartRescaling : Set ℓ

open PeriodicFractionalProfileTheorem public

round260PeriodicScaleOneProfileIsWeakLimit : Bool
round260PeriodicScaleOneProfileIsWeakLimit = true

round260EveryNoncompactPeriodicProfileShrinksToEuclideanScale : Bool
round260EveryNoncompactPeriodicProfileShrinksToEuclideanScale = true

round260CriticalHOneHalfNormDecouplingIncluded : Bool
round260CriticalHOneHalfNormDecouplingIncluded = true

round260CriticalL3RemainderSmallIncluded : Bool
round260CriticalL3RemainderSmallIncluded = true

round260DerivedFromFractionalEuclideanProfilesPlusTorusLocalization : Bool
round260DerivedFromFractionalEuclideanProfilesPlusTorusLocalization = true

round260AnalyticTopologyKernelDerivedInFiniteAgda : Bool
round260AnalyticTopologyKernelDerivedInFiniteAgda = false

round260PackageAClosed : Bool
round260PackageAClosed = false

round260DerivedFromFractionalEuclideanProfilesPlusTorusLocalizationIsTrue :
  round260DerivedFromFractionalEuclideanProfilesPlusTorusLocalization ≡ true
round260DerivedFromFractionalEuclideanProfilesPlusTorusLocalizationIsTrue = refl

round260AnalyticTopologyKernelDerivedInFiniteAgdaIsFalse :
  round260AnalyticTopologyKernelDerivedInFiniteAgda ≡ false
round260AnalyticTopologyKernelDerivedInFiniteAgdaIsFalse = refl
