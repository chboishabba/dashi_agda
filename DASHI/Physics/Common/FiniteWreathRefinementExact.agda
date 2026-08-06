module DASHI.Physics.Common.FiniteWreathRefinementExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
-- John D. Dixon and Brian Mortimer, "Permutation Groups".
-- DOI: 10.1007/978-1-4612-0731-3.
-- Volodymyr Nekrashevych, "Self-Similar Groups".
-- DOI: 10.1090/surv/117.
--
-- DASHI CONTRIBUTION
-- Executable finite witness of local state transformation combined with a
-- permutation of coarse indices.  This is a wreath-style schema only.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

data TriState : Set where
  negativeState : TriState
  neutralState : TriState
  positiveState : TriState

reverseTriState : TriState → TriState
reverseTriState negativeState = positiveState
reverseTriState neutralState = neutralState
reverseTriState positiveState = negativeState

reverseTriStateInvolutive :
  ∀ state → reverseTriState (reverseTriState state) ≡ state
reverseTriStateInvolutive negativeState = refl
reverseTriStateInvolutive neutralState = refl
reverseTriStateInvolutive positiveState = refl

data TwoSite : Set where
  leftSite : TwoSite
  rightSite : TwoSite

swapSite : TwoSite → TwoSite
swapSite leftSite = rightSite
swapSite rightSite = leftSite

Assignment : Set
Assignment = TwoSite → TriState

localPermutationStep : Assignment → Assignment
localPermutationStep assignment site =
  reverseTriState (assignment (swapSite site))

localPermutationStepTwiceAt :
  ∀ assignment site →
  localPermutationStep (localPermutationStep assignment) site ≡ assignment site
localPermutationStepTwiceAt assignment leftSite =
  reverseTriStateInvolutive (assignment leftSite)
localPermutationStepTwiceAt assignment rightSite =
  reverseTriStateInvolutive (assignment rightSite)
