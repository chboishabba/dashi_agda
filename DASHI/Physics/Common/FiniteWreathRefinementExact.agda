module DASHI.Physics.Common.FiniteWreathRefinementExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John D. Dixon and Brian Mortimer,
-- "Permutation Groups", Graduate Texts in Mathematics 163, Springer, 1996.
-- DOI: 10.1007/978-1-4612-0731-3.
--
-- Volodymyr Nekrashevych,
-- "Self-Similar Groups", Mathematical Surveys and Monographs 117,
-- American Mathematical Society, 2005.
-- DOI: 10.1090/surv/117.
--
-- DASHI CONTRIBUTION
--
-- Give an executable finite witness of the two ingredients of a wreath-style
-- action: independent local state transformations and a permutation of coarse
-- indices.  The witness is deliberately small and exact.  It does not identify
-- this finite action with any external physical or representation-theoretic
-- action.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)

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

swapSiteInvolutive : ∀ site → swapSite (swapSite site) ≡ site
swapSiteInvolutive leftSite = refl
swapSiteInvolutive rightSite = refl

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

canonicalAssignment : Assignment
canonicalAssignment leftSite = negativeState
canonicalAssignment rightSite = neutralState

canonicalStepLeft :
  localPermutationStep canonicalAssignment leftSite ≡ neutralState
canonicalStepLeft = refl

canonicalStepRight :
  localPermutationStep canonicalAssignment rightSite ≡ positiveState
canonicalStepRight = refl

record WreathRefinementBoundary : Set where
  constructor wreathRefinementBoundary
  field
    localTransformsAndIndexPermutationAreBothPresent : Bool
    localTransformsAndIndexPermutationAreBothPresentIsTrue :
      localTransformsAndIndexPermutationAreBothPresent ≡ true

    finiteWitnessConstructsExternalAction : Bool
    finiteWitnessConstructsExternalActionIsFalse :
      finiteWitnessConstructsExternalAction ≡ false

canonicalWreathRefinementBoundary : WreathRefinementBoundary
canonicalWreathRefinementBoundary =
  wreathRefinementBoundary true refl false refl
