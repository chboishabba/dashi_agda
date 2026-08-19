module DASHI.Physics.Closure.NSTriadKNStrongSixThreeLinearViscousNoGoRound89Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Piero D'Ancona.
-- Title: "A Short Proof of Commutator Estimates".
-- DOI: 10.1007/s00041-018-9612-8.
-- Correction DOI: 10.1007/s00041-019-09724-7.
--
-- ROUND89 / CRITICAL CORRECTION: SQUARED GRAM != LINEAR TRANSFER
--
-- The six-three strong branch is a SQUARED pair-product/commutator envelope.
-- The viscous relative-growth atom is linear in the signed transfer tau and
-- carries two high-frequency powers.  Thus a physical estimate
--
--     |tau|^2 <= g_s(d) M
--
-- would imply after weighting and squaring
--
--     |S_d^2 tau|^2 <= S_d^4 g_s(d) M,
--
-- not S_d^2 g_s(d) M.
--
-- The existing exact strong calibration is
--
--     g_s(d) S_d^3 = 1.
--
-- Hence this file proves
--
--     g_s(d) S_d^4 = S_d.
--
-- Since S_d doubles with the gap, the current strong squared branch is still
-- one full inverse separation power short even for pointwise scale balance of
-- the LINEAR two-derivative viscous transfer.  A summable far-gap theorem needs
-- strictly more decay again, or a cancellation that removes part of the
-- viscous weight before absolute-value/square majorization.
--
-- The earlier Round89 identity g_s S_d^2 = g_w remains true and useful for a
-- genuinely squared consumer; this module prevents it from being silently
-- promoted to the linear viscous-variation consumer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using (_*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality as Eq using (cong)
open Eq.≡-Reasoning

import DASHI.Physics.Closure.NSTriadKNLuoSixThreeCenteredCommutatorScaleExact as SixThree
import DASHI.Physics.Closure.NSTriadKNLuoFiniteEnergyCriticalScalingGapExact as Dyadic

strongSquaredBranchAfterLinearTwoDerivativeWeight :
  (gap : Nat) →
  SixThree.strongBranchSquaredGap gap
    * (SixThree.separationScale gap
      * SixThree.separationScale gap
      * SixThree.separationScale gap
      * SixThree.separationScale gap)
  ≡ SixThree.separationScale gap
strongSquaredBranchAfterLinearTwoDerivativeWeight gap =
  begin
    SixThree.strongBranchSquaredGap gap
      * (SixThree.separationScale gap
        * SixThree.separationScale gap
        * SixThree.separationScale gap
        * SixThree.separationScale gap)
  ≡⟨ solve
       ( SixThree.strongBranchSquaredGap gap
       ∷ SixThree.separationScale gap
       ∷ []) ⟩
    (SixThree.strongBranchSquaredGap gap
      * (SixThree.separationScale gap
        * SixThree.separationScale gap
        * SixThree.separationScale gap))
      * SixThree.separationScale gap
  ≡⟨ cong (_* SixThree.separationScale gap)
       (SixThree.strongGapCubicSeparationCalibration gap) ⟩
    Data.Rational.Base.1ℚ * SixThree.separationScale gap
  ≡⟨ solve (SixThree.separationScale gap ∷ []) ⟩
    SixThree.separationScale gap
  ∎

separationScaleDoubles :
  (gap : Nat) →
  SixThree.separationScale (suc gap)
  ≡ Dyadic.two * SixThree.separationScale gap
separationScaleDoubles gap =
  solve
    ( SixThree.four
    ∷ Dyadic.two
    ∷ Dyadic.dyadicScale gap
    ∷ [])

weightedStrongSquaredRequirementDoubles :
  (gap : Nat) →
  SixThree.strongBranchSquaredGap (suc gap)
    * (SixThree.separationScale (suc gap)
      * SixThree.separationScale (suc gap)
      * SixThree.separationScale (suc gap)
      * SixThree.separationScale (suc gap))
  ≡ Dyadic.two
      * (SixThree.strongBranchSquaredGap gap
        * (SixThree.separationScale gap
          * SixThree.separationScale gap
          * SixThree.separationScale gap
          * SixThree.separationScale gap))
weightedStrongSquaredRequirementDoubles gap =
  begin
    SixThree.strongBranchSquaredGap (suc gap)
      * (SixThree.separationScale (suc gap)
        * SixThree.separationScale (suc gap)
        * SixThree.separationScale (suc gap)
        * SixThree.separationScale (suc gap))
  ≡⟨ strongSquaredBranchAfterLinearTwoDerivativeWeight (suc gap) ⟩
    SixThree.separationScale (suc gap)
  ≡⟨ separationScaleDoubles gap ⟩
    Dyadic.two * SixThree.separationScale gap
  ≡⟨ cong (Dyadic.two *_)
       (Eq.sym (strongSquaredBranchAfterLinearTwoDerivativeWeight gap)) ⟩
    Dyadic.two
      * (SixThree.strongBranchSquaredGap gap
        * (SixThree.separationScale gap
          * SixThree.separationScale gap
          * SixThree.separationScale gap
          * SixThree.separationScale gap))
  ∎

round89StrongSquaredGramPaysLinearTwoDerivativeViscousWeight : Bool
round89StrongSquaredGramPaysLinearTwoDerivativeViscousWeight = false

round89LinearViscousConsumerNeedsAtLeastOneMoreSquaredGapPower : Bool
round89LinearViscousConsumerNeedsAtLeastOneMoreSquaredGapPower = true

round89D1SquaredGramCanDirectlyServeAsLinearVariationBound : Bool
round89D1SquaredGramCanDirectlyServeAsLinearVariationBound = false

round89StrongSquaredGramPaysLinearTwoDerivativeViscousWeightIsFalse :
  round89StrongSquaredGramPaysLinearTwoDerivativeViscousWeight ≡ false
round89StrongSquaredGramPaysLinearTwoDerivativeViscousWeightIsFalse = refl

round89LinearViscousConsumerNeedsAtLeastOneMoreSquaredGapPowerIsTrue :
  round89LinearViscousConsumerNeedsAtLeastOneMoreSquaredGapPower ≡ true
round89LinearViscousConsumerNeedsAtLeastOneMoreSquaredGapPowerIsTrue = refl

round89D1SquaredGramCanDirectlyServeAsLinearVariationBoundIsFalse :
  round89D1SquaredGramCanDirectlyServeAsLinearVariationBound ≡ false
round89D1SquaredGramCanDirectlyServeAsLinearVariationBoundIsFalse = refl
