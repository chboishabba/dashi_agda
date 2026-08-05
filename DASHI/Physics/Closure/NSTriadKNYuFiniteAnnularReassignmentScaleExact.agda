module DASHI.Physics.Closure.NSTriadKNYuFiniteAnnularReassignmentScaleExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier--Stokes Equations".
-- arXiv:2606.27560v1.
-- arXiv DOI: 10.48550/arXiv.2606.27560.
--
-- PURPOSE
-- Prove the exact squared scale identity behind Proposition 8.6.  Before
-- reassignment an annulus m steps away carries 2^(-3m/2), while changing the
-- reservoir normalization from r_k^{-1/2} to r_(k-m)^{-1/2} contributes
-- 2^(m/2).  Squaring removes all radicals:
--
--   2^(-3m) 2^m = 2^(-2m).
--
-- Thus the reassigned convolution kernel is 2^(-m), whose square is 4^(-m).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality as Eq using (cong)
open Eq.≡-Reasoning

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNLuoFiniteHighHighLowBernsteinGainExact as HH
import DASHI.Physics.Closure.NSTriadKNLuoFiniteEnergyCriticalScalingGapExact as Scale

inverseRadiusRatio : Nat → ℚ
inverseRadiusRatio = Scale.dyadicScale

squaredReassignedKernel : Nat → ℚ
squaredReassignedKernel = Geo.pow Geo.quarter

annularReassignmentScaleIdentity :
  (gap : Nat) →
  HH.squaredBernsteinGapGain gap * inverseRadiusRatio gap
  ≡ squaredReassignedKernel gap
annularReassignmentScaleIdentity zero = refl
annularReassignmentScaleIdentity (suc gap) =
  begin
    HH.squaredBernsteinGapGain (suc gap)
      * inverseRadiusRatio (suc gap)
  ≡⟨ solve
       ( HH.oneEighth
       ∷ Scale.two
       ∷ HH.squaredBernsteinGapGain gap
       ∷ inverseRadiusRatio gap
       ∷ []) ⟩
    Geo.quarter
      * (HH.squaredBernsteinGapGain gap * inverseRadiusRatio gap)
  ≡⟨ cong (Geo.quarter *_) (annularReassignmentScaleIdentity gap) ⟩
    Geo.quarter * squaredReassignedKernel gap
  ≡⟨ refl ⟩
    squaredReassignedKernel (suc gap)
  ∎
