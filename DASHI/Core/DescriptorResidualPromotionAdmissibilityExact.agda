module DASHI.Core.DescriptorResidualPromotionAdmissibilityExact where

open import DASHI.Core.Prelude

import DASHI.Core.ObserverRefinementLatticeExact as Observer

------------------------------------------------------------------------
-- DESCRIPTOR / RESIDUAL / PROMOTION-ADMISSIBILITY CORE
--
-- A coarse descriptor may collide on two states while a retained residual
-- separates them and a proposed promotion/transport is admissible for one but
-- blocked for the other.  In that case the coarse descriptor cannot determine
-- promotion admissibility.
--
-- This is domain-neutral: a promotion can mean an allowed physical transition,
-- an evidence-qualified claim transport, a representation identification, etc.
------------------------------------------------------------------------

record HiddenResidualPromotion
    {State Descriptor Residual Promotion : Set}
    (descriptor : Observer.Observer State Descriptor)
    (residual : Observer.Observer State Residual)
    (Admissible : Promotion → State → Set)
    (promotion : Promotion) : Set where
  constructor hidden-residual-promotion
  field
    left right : State
    sameDescriptor : descriptor left ≡ descriptor right
    residualSeparates : residual left ≡ residual right → ⊥
    admissibleLeft : Admissible promotion left
    blockedRight : Admissible promotion right → ⊥

open HiddenResidualPromotion public

DescriptorDeterminesPromotion :
  ∀ {State Descriptor Promotion : Set} →
  Observer.Observer State Descriptor →
  (Promotion → State → Set) →
  Promotion →
  Set
DescriptorDeterminesPromotion descriptor Admissible promotion =
  ∀ x y →
  descriptor x ≡ descriptor y →
  Admissible promotion x →
  Admissible promotion y

hiddenResidualPromotionBlocksDescriptorDetermination :
  ∀ {State Descriptor Residual Promotion : Set}
    {descriptor : Observer.Observer State Descriptor}
    {residual : Observer.Observer State Residual}
    {Admissible : Promotion → State → Set}
    {promotion : Promotion} →
  HiddenResidualPromotion descriptor residual Admissible promotion →
  DescriptorDeterminesPromotion descriptor Admissible promotion →
  ⊥
hiddenResidualPromotionBlocksDescriptorDetermination witness determines =
  blockedRight witness
    (determines
      (left witness)
      (right witness)
      (sameDescriptor witness)
      (admissibleLeft witness))

refinedPromotionObserver :
  ∀ {State Descriptor Residual : Set} →
  Observer.Observer State Descriptor →
  Observer.Observer State Residual →
  Observer.Observer State (Descriptor × Residual)
refinedPromotionObserver = Observer.pairObserver

hiddenResidualPromotionGivesStrictRefinement :
  ∀ {State Descriptor Residual Promotion : Set}
    {descriptor : Observer.Observer State Descriptor}
    {residual : Observer.Observer State Residual}
    {Admissible : Promotion → State → Set}
    {promotion : Promotion} →
  HiddenResidualPromotion descriptor residual Admissible promotion →
  Observer.StrictRefinement
    descriptor
    (refinedPromotionObserver descriptor residual)
hiddenResidualPromotionGivesStrictRefinement witness =
  Observer.strictPairRefinement
    _ _
    (left witness)
    (right witness)
    (sameDescriptor witness)
    (residualSeparates witness)

------------------------------------------------------------------------
-- BIDI reverse obligation.
--
-- To promote a rule saying that a coarse descriptor determines admissibility,
-- one must rule out every same-descriptor residual collision that changes the
-- admissibility judgement.  Descriptor equality alone never supplies this.
------------------------------------------------------------------------

record PromotionAdmissibilityBoundary : Set where
  constructor promotion-admissibility-boundary
  field
    sameDescriptorAutomaticallySamePromotionAuthority : Bool
    sameDescriptorAutomaticallySamePromotionAuthorityIsFalse :
      sameDescriptorAutomaticallySamePromotionAuthority ≡ false

    residualCanStrictlyRefineDescriptor : Bool
    residualCanStrictlyRefineDescriptorIsTrue :
      residualCanStrictlyRefineDescriptor ≡ true

    admissibilityDifferenceCanBlockDescriptorDescent : Bool
    admissibilityDifferenceCanBlockDescriptorDescentIsTrue :
      admissibilityDifferenceCanBlockDescriptorDescent ≡ true

    strictRefinementAutomaticallyProvesDomainCausality : Bool
    strictRefinementAutomaticallyProvesDomainCausalityIsFalse :
      strictRefinementAutomaticallyProvesDomainCausality ≡ false

canonicalPromotionAdmissibilityBoundary : PromotionAdmissibilityBoundary
canonicalPromotionAdmissibilityBoundary =
  promotion-admissibility-boundary false refl true refl true refl false refl
