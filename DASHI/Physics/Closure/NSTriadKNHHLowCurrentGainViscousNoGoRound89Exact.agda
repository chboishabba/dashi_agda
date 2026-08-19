module DASHI.Physics.Closure.NSTriadKNHHLowCurrentGainViscousNoGoRound89Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Terence Tao.
-- Title: "Finite Time Blowup for an Averaged Three-Dimensional
-- Navier--Stokes Equation".
-- DOI: 10.1090/jams/838.
--
-- ROUND89 / ROUTE-KILLER FOR THE CURRENT HH->LOW GAIN
--
-- The repository's existing HH->low scale theorem has the unsquared gain
--
--     h(d) = 2^-d,
--
-- characterized exactly by h(d) 2^d = 1.  The Round88 viscous relative-growth
-- spread costs two high-frequency separation powers.  With
--
--     S_d = 4 * 2^d,
--
-- this file proves
--
--     h(d) S_d     = 4,
--     h(d) S_d^2   = 4 S_d.
--
-- Since S_{d+1}=2 S_d, the two-power weighted current HH gain doubles with the
-- gap.  Therefore the existing 2^-d HH->low estimate CANNOT supply a
-- cutoff-uniform far-gap viscous-variation bound.
--
-- This falsifies the tempting carrier identification
--
--     current HH->low gain = strong six-three Com branch.
--
-- The latter has squared decay 2^-3d and really can pay two separation powers;
-- it belongs to the centered low-high Com calculation.  A successful HH
-- viscous route now requires a NEW physical cancellation theorem producing at
-- least two additional inverse high-frequency powers (or a different
-- mechanism that removes the quadratic viscous spread before majorization).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 1ℚ; _/_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality as Eq using (cong; trans)
open Eq.≡-Reasoning

import DASHI.Physics.Closure.NSTriadKNLuoFiniteHighHighLowDyadicGainExact as HH
import DASHI.Physics.Closure.NSTriadKNLuoFiniteNearWindowScalingObstructionExact as Reciprocal
import DASHI.Physics.Closure.NSTriadKNLuoFiniteEnergyCriticalScalingGapExact as Dyadic
import DASHI.Physics.Closure.NSTriadKNLuoSixThreeCenteredCommutatorScaleExact as SixThree

four : ℚ
four = Int.+ 4 / 1

currentHHGainTimesOneSeparationScale :
  (gap : Nat) →
  HH.highHighLowGain gap * SixThree.separationScale gap ≡ four
currentHHGainTimesOneSeparationScale gap =
  begin
    HH.highHighLowGain gap * SixThree.separationScale gap
  ≡⟨ solve
       ( HH.highHighLowGain gap
       ∷ four
       ∷ Dyadic.dyadicScale gap
       ∷ []) ⟩
    four * (HH.highHighLowGain gap * Dyadic.dyadicScale gap)
  ≡⟨ cong (four *_)
       (Reciprocal.reciprocalDyadicIdentity gap) ⟩
    four * 1ℚ
  ≡⟨ solve [] ⟩
    four
  ∎

currentHHGainTimesTwoSeparationPowers :
  (gap : Nat) →
  HH.highHighLowGain gap
    * (SixThree.separationScale gap * SixThree.separationScale gap)
  ≡ four * SixThree.separationScale gap
currentHHGainTimesTwoSeparationPowers gap =
  begin
    HH.highHighLowGain gap
      * (SixThree.separationScale gap * SixThree.separationScale gap)
  ≡⟨ solve
       ( HH.highHighLowGain gap
       ∷ SixThree.separationScale gap
       ∷ []) ⟩
    (HH.highHighLowGain gap * SixThree.separationScale gap)
      * SixThree.separationScale gap
  ≡⟨ cong (_* SixThree.separationScale gap)
       (currentHHGainTimesOneSeparationScale gap) ⟩
    four * SixThree.separationScale gap
  ∎

separationScaleDoubles :
  (gap : Nat) →
  SixThree.separationScale (suc gap)
  ≡ Dyadic.two * SixThree.separationScale gap
separationScaleDoubles gap =
  solve
    ( four
    ∷ Dyadic.two
    ∷ Dyadic.dyadicScale gap
    ∷ [])

weightedCurrentHHGainDoubles :
  (gap : Nat) →
  HH.highHighLowGain (suc gap)
    * (SixThree.separationScale (suc gap)
      * SixThree.separationScale (suc gap))
  ≡ Dyadic.two
      * (HH.highHighLowGain gap
        * (SixThree.separationScale gap
          * SixThree.separationScale gap))
weightedCurrentHHGainDoubles gap =
  begin
    HH.highHighLowGain (suc gap)
      * (SixThree.separationScale (suc gap)
        * SixThree.separationScale (suc gap))
  ≡⟨ currentHHGainTimesTwoSeparationPowers (suc gap) ⟩
    four * SixThree.separationScale (suc gap)
  ≡⟨ cong (four *_) (separationScaleDoubles gap) ⟩
    four * (Dyadic.two * SixThree.separationScale gap)
  ≡⟨ solve (four ∷ Dyadic.two ∷ SixThree.separationScale gap ∷ []) ⟩
    Dyadic.two * (four * SixThree.separationScale gap)
  ≡⟨ cong (Dyadic.two *_)
       (Eq.sym (currentHHGainTimesTwoSeparationPowers gap)) ⟩
    Dyadic.two
      * (HH.highHighLowGain gap
        * (SixThree.separationScale gap
          * SixThree.separationScale gap))
  ∎

round89ExistingHHLowGainPaysTwoViscousPowers : Bool
round89ExistingHHLowGainPaysTwoViscousPowers = false

round89StrongComBranchCanBeIdentifiedWithCurrentHHLowGain : Bool
round89StrongComBranchCanBeIdentifiedWithCurrentHHLowGain = false

round89HHViscousRouteNeedsAdditionalCancellationPowers : Bool
round89HHViscousRouteNeedsAdditionalCancellationPowers = true

round89ExistingHHLowGainPaysTwoViscousPowersIsFalse :
  round89ExistingHHLowGainPaysTwoViscousPowers ≡ false
round89ExistingHHLowGainPaysTwoViscousPowersIsFalse = refl

round89StrongComBranchCanBeIdentifiedWithCurrentHHLowGainIsFalse :
  round89StrongComBranchCanBeIdentifiedWithCurrentHHLowGain ≡ false
round89StrongComBranchCanBeIdentifiedWithCurrentHHLowGainIsFalse = refl

round89HHViscousRouteNeedsAdditionalCancellationPowersIsTrue :
  round89HHViscousRouteNeedsAdditionalCancellationPowers ≡ true
round89HHViscousRouteNeedsAdditionalCancellationPowersIsTrue = refl
