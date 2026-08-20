module DASHI.Physics.Closure.NSTriadKNAdverseMaskCancellationNoGoExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- DASHI MAKE-OR-BREAK AUDIT
--
-- Round106 correctly retained the SIGN of the external Waleffe forcing on
-- each adverse phase episode.  However the adverse set is triad dependent:
-- every channel is multiplied by its own indicator 1_{A_tau >= 0}.
-- Consequently an unmasked complete-network cancellation does NOT, by itself,
-- survive adverse restriction.
--
-- This file proves the obstruction in the smallest exact finite model.  Two
-- equally weighted channels may cancel perfectly,
--
--      f_1 + f_2 = x + (-x) = 0,
--
-- while independent adverse masks keep the first and suppress the second,
--
--      1*f_1 + 0*f_2 = x > 0.
--
-- Thus a future proof may use complete-network cancellation only if it ALSO
-- proves a physical relation between the channel masks/phases, or proves an
-- unconditional masked operator estimate.  Pointwise telescoping of the
-- unmasked forcing is not a sufficient Clay mechanism.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary.Negation.Core using (¬_)

record TwoChannelMaskedForcing : Set where
  constructor two-channel-masked-forcing
  field
    weight₁ weight₂ forcing₁ forcing₂ mask₁ mask₂ : ℚ

open TwoChannelMaskedForcing public

unmaskedWeightedForcing : TwoChannelMaskedForcing → ℚ
unmaskedWeightedForcing C =
  weight₁ C * forcing₁ C + weight₂ C * forcing₂ C

maskedWeightedForcing : TwoChannelMaskedForcing → ℚ
maskedWeightedForcing C =
  mask₁ C * (weight₁ C * forcing₁ C)
  + mask₂ C * (weight₂ C * forcing₂ C)

cancellingOppositePair : ℚ → TwoChannelMaskedForcing
cancellingOppositePair x =
  two-channel-masked-forcing 1ℚ 1ℚ x (- x) 1ℚ 0ℚ

oppositePairCancelsBeforeMask :
  (x : ℚ) →
  unmaskedWeightedForcing (cancellingOppositePair x) ≡ 0ℚ
oppositePairCancelsBeforeMask x = solve (x ∷ [])

oppositePairMaskKeepsFirst :
  (x : ℚ) →
  maskedWeightedForcing (cancellingOppositePair x) ≡ x
oppositePairMaskKeepsFirst x = solve (x ∷ [])

maskedForcingCanBePositiveDespiteExactNetworkCancellation :
  (x : ℚ) →
  0ℚ < x →
  0ℚ < maskedWeightedForcing (cancellingOppositePair x)
maskedForcingCanBePositiveDespiteExactNetworkCancellation x xPositive
  rewrite oppositePairMaskKeepsFirst x = xPositive

zeroCancellationResidualCannotBoundMaskedForcing :
  (x : ℚ) →
  0ℚ < x →
  ¬ (maskedWeightedForcing (cancellingOppositePair x) ≤ 0ℚ)
zeroCancellationResidualCannotBoundMaskedForcing x xPositive maskedNonpositive =
  ℚP.<-irrefl 0ℚ
    (ℚP.<-≤-trans
      (maskedForcingCanBePositiveDespiteExactNetworkCancellation x xPositive)
      maskedNonpositive)

roundTripWitnessAtOne :
  unmaskedWeightedForcing (cancellingOppositePair 1ℚ) ≡ 0ℚ
  × maskedWeightedForcing (cancellingOppositePair 1ℚ) ≡ 1ℚ
roundTripWitnessAtOne =
  oppositePairCancelsBeforeMask 1ℚ , oppositePairMaskKeepsFirst 1ℚ
  where
  open import Data.Product.Base using (_×_; _,_)

adverseMaskCanDestroyExactNetworkCancellation : Bool
adverseMaskCanDestroyExactNetworkCancellation = true

unmaskedTelescopingAloneCanCloseAdverseEpisodeBudget : Bool
unmaskedTelescopingAloneCanCloseAdverseEpisodeBudget = false

adverseMaskCanDestroyExactNetworkCancellationIsTrue :
  adverseMaskCanDestroyExactNetworkCancellation ≡ true
adverseMaskCanDestroyExactNetworkCancellationIsTrue = refl

unmaskedTelescopingAloneCanCloseAdverseEpisodeBudgetIsFalse :
  unmaskedTelescopingAloneCanCloseAdverseEpisodeBudget ≡ false
unmaskedTelescopingAloneCanCloseAdverseEpisodeBudgetIsFalse = refl
