module DASHI.Core.RelevanceDistortionRefinement where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- RELEVANCE DENSITY != BEHAVIOURAL DISTORTION
--
-- Reference / motivation:
--   Fernando E. Rosas,
--   "Adaptive state-action abstractions via rate-distortion", 2026.
--   arXiv:2606.06123.  DOI: no DOI assigned/listed on the arXiv record.
--
-- Rosas decomposes performance error into a learning-error term and an
-- abstraction-error term bounded using a bisimulation metric, and refines an
-- abstraction when the abstraction floor becomes comparable to remaining
-- learning error.  DASHI keeps that distortion axis separate from its own
-- consumer-relevance/ambient-carrier ratio.
------------------------------------------------------------------------

record RelevanceCompressionProfile (Carrier : Set) : Set₁ where
  constructor relevanceCompressionProfile
  field
    RelevanceMass : Set
    AmbientCost : Set
    relevanceMass : Carrier → RelevanceMass
    ambientCost : Carrier → AmbientCost

open RelevanceCompressionProfile public

record BehaviouralDistortionProfile (Projection : Set) : Set₁ where
  constructor behaviouralDistortionProfile
  field
    Distortion : Set
    distortion : Projection → Distortion

open BehaviouralDistortionProfile public

------------------------------------------------------------------------
-- No promotion: high/complete represented relevance does not itself prove low
-- behavioural distortion, just as full represented mass does not prove dynamic
-- quotient safety in ConsumerProjectionSufficiency.
------------------------------------------------------------------------

data HighRelevanceImpliesLowDistortionPermission : Set where

highRelevanceCannotAutomaticallyAssertLowDistortion :
  HighRelevanceImpliesLowDistortionPermission → ⊥
highRelevanceCannotAutomaticallyAssertLowDistortion ()

------------------------------------------------------------------------
-- Rate-distortion optimisation is represented as an application-supplied
-- certificate, not a fake theorem over arbitrary Rate/Distortion carriers.
------------------------------------------------------------------------

record RateDistortionOrder (Projection Rate Distortion : Set) : Set₁ where
  constructor rateDistortionOrder
  field
    rate : Projection → Rate
    distortion : Projection → Distortion
    AcceptableDistortion : Distortion → Set
    NoHigherRate : Rate → Rate → Set

open RateDistortionOrder public

record ConstrainedRateDistortionOptimum
    {Projection Rate Distortion : Set}
    (order : RateDistortionOrder Projection Rate Distortion) : Set₁ where
  constructor constrainedRateDistortionOptimum
  field
    chosenProjection : Projection
    chosenDistortionAcceptable :
      AcceptableDistortion order (distortion order chosenProjection)
    rateMinimalAmongAcceptable :
      (other : Projection) →
      AcceptableDistortion order (distortion order other) →
      NoHigherRate order
        (rate order chosenProjection)
        (rate order other)

open ConstrainedRateDistortionOptimum public

------------------------------------------------------------------------
-- Adaptive refinement trigger.
--
-- The relation ComparableForRefinement is application-supplied because DASHI
-- does not assume numeric errors globally.  An inhabited trigger says the
-- remaining inference/learning error has reached the abstraction-error floor,
-- at which point changing the carrier/quotient is warranted rather than only
-- improving inference inside the existing boxes.
------------------------------------------------------------------------

record AdaptiveRefinementSystem (Resolution Error : Set) : Set₁ where
  constructor adaptiveRefinementSystem
  field
    learningError : Resolution → Error
    abstractionError : Resolution → Error
    ComparableForRefinement : Error → Error → Set
    refine : Resolution → Resolution

open AdaptiveRefinementSystem public

record RefinementTriggered
    {Resolution Error : Set}
    (system : AdaptiveRefinementSystem Resolution Error)
    (resolution : Resolution) : Set where
  constructor refinementTriggered
  field
    errorsComparable :
      ComparableForRefinement system
        (learningError system resolution)
        (abstractionError system resolution)

open RefinementTriggered public

------------------------------------------------------------------------
-- Finite independence witness: two abstractions can have identical relevance
-- status while differing on behavioural distortion.
------------------------------------------------------------------------

data DemoProjection : Set where
  sameRelevanceLowDistortion sameRelevanceHighDistortion : DemoProjection

data DemoDistortion : Set where
  lowDistortion highDistortion : DemoDistortion

representedRelevanceIsComplete : DemoProjection → Bool
representedRelevanceIsComplete sameRelevanceLowDistortion = true
representedRelevanceIsComplete sameRelevanceHighDistortion = true

demoDistortion : DemoProjection → DemoDistortion
demoDistortion sameRelevanceLowDistortion = lowDistortion
demoDistortion sameRelevanceHighDistortion = highDistortion

lowIsNotHigh : lowDistortion ≡ highDistortion → ⊥
lowIsNotHigh ()

sameRelevanceCanCarryDifferentDistortion :
  representedRelevanceIsComplete sameRelevanceLowDistortion ≡
  representedRelevanceIsComplete sameRelevanceHighDistortion
sameRelevanceCanCarryDifferentDistortion = refl

behaviouralDistortionStillDiffers :
  demoDistortion sameRelevanceLowDistortion ≡
  demoDistortion sameRelevanceHighDistortion → ⊥
behaviouralDistortionStillDiffers = lowIsNotHigh
