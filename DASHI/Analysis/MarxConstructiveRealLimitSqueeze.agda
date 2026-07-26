module DASHI.Analysis.MarxConstructiveRealLimitSqueeze where

open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Primitive using (Set; Set₁)
open import Data.Product using (_×_; _,_)

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

    epsilonDeltaStatement :
      ∀ epsilon →
      PositiveRadius epsilon →
      Σ (Real R)
        (λ delta →
          PositiveRadius delta
          ×
          (∀ y →
            _<_ R (distance R x y) delta →
            _<_ R (distance R (f x) (f y)) epsilon))

open EpsilonContinuityAt public

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
