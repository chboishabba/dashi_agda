module DASHI.Physics.Foundations.TransitionActionNonseparabilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Generic transition-action discrimination.
--
-- A function of two endpoints need not encode a genuine interaction between
-- them: it may factor as L(left) + R(right).  This owner makes that distinction
-- explicit so pair-valued carriers are not automatically promoted to
-- relational transition geometry.
------------------------------------------------------------------------

record TransitionActionKernel : Set₁ where
  field
    State : Set
    localAction : State → State → Nat
    kernelReading : String

open TransitionActionKernel public

record EndpointSeparable (surface : TransitionActionKernel) : Set₁ where
  field
    leftPotential : State surface → Nat
    rightPotential : State surface → Nat
    decomposition :
      (left right : State surface) →
      localAction surface left right
      ≡
      leftPotential left + rightPotential right

open EndpointSeparable public

NonseparableTransition : TransitionActionKernel → Set₁
NonseparableTransition surface = EndpointSeparable surface → ⊥

record TransitionActionTarget : Set₁ where
  field
    kernel : TransitionActionKernel
    nonseparable : NonseparableTransition kernel
    targetReading : String

open TransitionActionTarget public

endpointSeparableBlocksNonseparableTarget :
  {surface : TransitionActionKernel} →
  EndpointSeparable surface →
  NonseparableTransition surface →
  ⊥
endpointSeparableBlocksNonseparableTarget separable nonseparable =
  nonseparable separable

record TransitionActionNonPromotionBoundary : Set where
  constructor transitionActionNonPromotionBoundary
  field
    twoArgumentFunctionImpliesInteraction : Bool
    twoArgumentFunctionImpliesInteractionIsFalse :
      twoArgumentFunctionImpliesInteraction ≡ false

    endpointSeparableKernelIsAlreadyRelationalAction : Bool
    endpointSeparableKernelIsAlreadyRelationalActionIsFalse :
      endpointSeparableKernelIsAlreadyRelationalAction ≡ false

    nonseparabilityAloneSuppliesPhysicalCalibration : Bool
    nonseparabilityAloneSuppliesPhysicalCalibrationIsFalse :
      nonseparabilityAloneSuppliesPhysicalCalibration ≡ false

canonicalTransitionActionNonPromotionBoundary :
  TransitionActionNonPromotionBoundary
canonicalTransitionActionNonPromotionBoundary =
  transitionActionNonPromotionBoundary
    false refl
    false refl
    false refl
