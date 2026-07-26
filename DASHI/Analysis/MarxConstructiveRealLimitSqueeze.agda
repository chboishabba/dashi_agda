module DASHI.Analysis.MarxConstructiveRealLimitSqueeze where

open import Agda.Primitive using (Set; Set₁)

open import DASHI.Analysis.ConstructiveRealSpine
open import DASHI.Analysis.MarxConstructiveRealTopology

------------------------------------------------------------------------
-- Squeeze and sequential/epsilon compatibility are isolated because they are
-- order-topology theorems, not consequences of Cauchy completeness alone.

record ConstructedRealSqueezeLimit
  (R : ConstructedOrderedCompleteReal)
  (L : ConstructedRealSequentialLimitLaws R)
  : Set₁ where
  field
    squeezeLimit :
      ∀ {lower middle upper limit} →
      ConvergesTo R lower limit →
      ConvergesTo R upper limit →
      (∀ n →
        _≤_ R
          (sequenceAt R lower n)
          (sequenceAt R middle n)) →
      (∀ n →
        _≤_ R
          (sequenceAt R middle n)
          (sequenceAt R upper n)) →
      ConvergesTo R middle limit

open ConstructedRealSqueezeLimit public

record EpsilonContinuityAt
  (R : ConstructedOrderedCompleteReal)
  (f : Real R → Real R)
  (x : Real R)
  : Set₁ where
  field
    PositiveRadius : Real R → Set
    epsilonDeltaStatement : Set

record SequentialEpsilonContinuityBridge
  (R : ConstructedOrderedCompleteReal)
  (L : ConstructedRealSequentialLimitLaws R)
  : Set₁ where
  field
    sequentialContinuityImpliesEpsilon :
      ∀ f x →
      ContinuousAtSequentially R L f x →
      EpsilonContinuityAt R f x

    epsilonContinuityImpliesSequential :
      ∀ f x →
      EpsilonContinuityAt R f x →
      ContinuousAtSequentially R L f x

open SequentialEpsilonContinuityBridge public

sequentialContinuityIffEpsilonContinuity :
  ∀ {R : ConstructedOrderedCompleteReal}
    {L : ConstructedRealSequentialLimitLaws R} →
  SequentialEpsilonContinuityBridge R L →
  ∀ f x →
  (ContinuousAtSequentially R L f x → EpsilonContinuityAt R f x)
  ×
  (EpsilonContinuityAt R f x → ContinuousAtSequentially R L f x)
sequentialContinuityIffEpsilonContinuity bridge f x =
  sequentialContinuityImpliesEpsilon bridge f x ,
  epsilonContinuityImpliesSequential bridge f x
  where
    infixr 4 _×_
    record _×_ (A B : Set) : Set where
      constructor _,_
      field
        first : A
        second : B
