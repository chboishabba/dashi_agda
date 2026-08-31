module DASHI.Core.ContextGovernedSafetyTransportExact where

------------------------------------------------------------------------
-- GOVERNED SAFETY TRANSPORT ACROSS CONTEXT / QUERY CHANGES
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerIndexedResidualRefinementExact as Consumer
import DASHI.Core.ContextIndexedGovernedObservationExact as Governed
import DASHI.Core.ContextIndexedObservationFibrationExact as Fibration
import DASHI.Core.ProjectionCategory as Cat

RequirementTransport :
  ∀ {State Context Query Surface}
    {observe : State → Surface} →
  (family : Governed.ContextIndexedGovernedFamily
    State Context Query Surface observe) →
  Context → Query → Context → Query → Set
RequirementTransport family sourceContext sourceQuery targetContext targetQuery =
  (axis : Governed.Axis family) →
  Governed.Active family targetContext targetQuery axis →
  Governed.Active family sourceContext sourceQuery axis

governedSafetyTransportsWhenTargetRequirementsAreInherited :
  ∀ {State Context Query Surface}
    {observe : State → Surface}
    {family : Governed.ContextIndexedGovernedFamily
      State Context Query Surface observe}
    {sourceContext targetContext : Context}
    {sourceQuery targetQuery : Query} →
  RequirementTransport
    family sourceContext sourceQuery targetContext targetQuery →
  Governed.GovernedSafeFor family sourceContext sourceQuery →
  Governed.GovernedSafeFor family targetContext targetQuery
governedSafetyTransportsWhenTargetRequirementsAreInherited
  transport sourceSafe axis activeTarget =
  sourceSafe axis (transport axis activeTarget)

record NewlyActivatedGovernedAxis
    {State Context Query Surface}
    {observe : State → Surface}
    (family : Governed.ContextIndexedGovernedFamily
      State Context Query Surface observe)
    (sourceContext : Context)
    (sourceQuery : Query)
    (targetContext : Context)
    (targetQuery : Query) : Set₁ where
  constructor newly-activated-governed-axis
  field
    axis : Governed.Axis family
    inactiveAtSource :
      Governed.Active family sourceContext sourceQuery axis → ⊥
    activeAtTarget :
      Governed.Active family targetContext targetQuery axis
    targetCollision :
      Consumer.ConsumerRelevantCollision
        observe (Governed.consume family axis)

open NewlyActivatedGovernedAxis public

newlyActivatedCollisionBlocksTargetSafety :
  ∀ {State Context Query Surface}
    {observe : State → Surface}
    {family : Governed.ContextIndexedGovernedFamily
      State Context Query Surface observe}
    {sourceContext targetContext : Context}
    {sourceQuery targetQuery : Query} →
  NewlyActivatedGovernedAxis
    family sourceContext sourceQuery targetContext targetQuery →
  Governed.GovernedSafeFor family targetContext targetQuery →
  ⊥
newlyActivatedCollisionBlocksTargetSafety newly safe =
  Consumer.coarseCollisionBlocksSufficiency
    (targetCollision newly)
    (safe (axis newly) (activeAtTarget newly))

record IndexedGovernedConsumer
    {base : Cat.ProjectionCategory}
    (indexed : Fibration.ContextIndexedObservation base) : Set₁ where
  field
    Axis : Set
    Outcome : Cat.Obj base → Axis → Set
    consume :
      (context : Cat.Obj base) →
      (axis : Axis) →
      Fibration.Fine indexed context → Outcome context axis

open IndexedGovernedConsumer public

record GovernedConsumerRestriction
    {base : Cat.ProjectionCategory}
    {indexed : Fibration.ContextIndexedObservation base}
    (consumer : IndexedGovernedConsumer indexed)
    {A B : Cat.Obj base}
    (change : Cat.Hom base A B) : Set₁ where
  field
    restrictOutcome :
      (axis : Axis consumer) →
      Outcome consumer B axis → Outcome consumer A axis
    consumerNaturality :
      (axis : Axis consumer) →
      (x : Fibration.Fine indexed B) →
      consume consumer A axis (Fibration.restrictFine indexed change x)
      ≡ restrictOutcome axis (consume consumer B axis x)

open GovernedConsumerRestriction public

RestrictedImageSufficient :
  ∀ {base : Cat.ProjectionCategory}
    {indexed : Fibration.ContextIndexedObservation base}
    (consumer : IndexedGovernedConsumer indexed)
    {A B : Cat.Obj base}
    (change : Cat.Hom base A B)
    (axis : Axis consumer) → Set
RestrictedImageSufficient {indexed = indexed} consumer {A} {B} change axis =
  ∀ x y →
  Fibration.observe indexed A (Fibration.restrictFine indexed change x)
  ≡ Fibration.observe indexed A (Fibration.restrictFine indexed change y) →
  consume consumer A axis (Fibration.restrictFine indexed change x)
  ≡ consume consumer A axis (Fibration.restrictFine indexed change y)

localSafetyControlsRestrictedImage :
  ∀ {base : Cat.ProjectionCategory}
    {indexed : Fibration.ContextIndexedObservation base}
    (consumer : IndexedGovernedConsumer indexed)
    {A B : Cat.Obj base}
    (change : Cat.Hom base A B)
    (axis : Axis consumer) →
  Consumer.ConsumerSufficient
    (Fibration.observe indexed A)
    (consume consumer A axis) →
  RestrictedImageSufficient consumer change axis
localSafetyControlsRestrictedImage {indexed = indexed} consumer change axis safe x y same =
  safe
    (Fibration.restrictFine indexed change x)
    (Fibration.restrictFine indexed change y)
    same

record RestrictionCoversFine
    {base : Cat.ProjectionCategory}
    (indexed : Fibration.ContextIndexedObservation base)
    {A B : Cat.Obj base}
    (change : Cat.Hom base A B) : Set₁ where
  field
    liftFine : Fibration.Fine indexed A → Fibration.Fine indexed B
    liftRestrictsBack :
      (x : Fibration.Fine indexed A) →
      Fibration.restrictFine indexed change (liftFine x) ≡ x

open RestrictionCoversFine public

restrictedImageSafetyPromotesWithCoverage :
  ∀ {base : Cat.ProjectionCategory}
    {indexed : Fibration.ContextIndexedObservation base}
    (consumer : IndexedGovernedConsumer indexed)
    {A B : Cat.Obj base}
    (change : Cat.Hom base A B)
    (axis : Axis consumer) →
  RestrictionCoversFine indexed change →
  RestrictedImageSufficient consumer change axis →
  Consumer.ConsumerSufficient
    (Fibration.observe indexed A)
    (consume consumer A axis)
restrictedImageSafetyPromotesWithCoverage
  {indexed = indexed} consumer {A} {B} change axis coverage restrictedSafe x y same =
  trans
    (sym (cong (consume consumer A axis) (liftRestrictsBack coverage x)))
    (trans
      (restrictedSafe
        (liftFine coverage x)
        (liftFine coverage y)
        (trans
          (cong (Fibration.observe indexed A) (liftRestrictsBack coverage x))
          (trans same
            (sym (cong (Fibration.observe indexed A)
              (liftRestrictsBack coverage y))))))
      (cong (consume consumer A axis) (liftRestrictsBack coverage y)))

record ContextGovernedSafetyTransportBoundary : Set where
  field
    targetRequirementsMustBeInheritedOrReproved : Bool
    newlyActivatedCollidingAxisCanBreakTransport : Bool
    observationNaturalityAloneImpliesGlobalSafetyTransport : Bool
    localSafetyControlsRestrictedImageExactly : Bool
    imageSafetyNeedsCoverageForWholeContextPromotion : Bool

canonicalContextGovernedSafetyTransportBoundary :
  ContextGovernedSafetyTransportBoundary
canonicalContextGovernedSafetyTransportBoundary = record
  { targetRequirementsMustBeInheritedOrReproved = true
  ; newlyActivatedCollidingAxisCanBreakTransport = true
  ; observationNaturalityAloneImpliesGlobalSafetyTransport = false
  ; localSafetyControlsRestrictedImageExactly = true
  ; imageSafetyNeedsCoverageForWholeContextPromotion = true
  }
