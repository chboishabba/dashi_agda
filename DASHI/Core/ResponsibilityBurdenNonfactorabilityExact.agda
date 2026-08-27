module DASHI.Core.ResponsibilityBurdenNonfactorabilityExact where

------------------------------------------------------------------------
-- RESPONSIBILITY / BURDEN NONFACTORABILITY
--
-- Aggregate harm or overshoot does not determine who contributed to a problem
-- and who bears its consequences.  Contribution and burden are separate axes.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Core.ConsumerDescentMinimalObserverExact as Consumer

record ResponsibilityBurdenGeometry (Population Aggregate Contribution Burden : Set) : Set₁ where
  constructor responsibilityBurdenGeometry
  field
    aggregateObserver : Population → Aggregate
    contribution : Population → Contribution
    burden : Population → Burden

open ResponsibilityBurdenGeometry public

record AggregateResponsibilityLoss
    {Population Aggregate Contribution Burden : Set}
    (geometry : ResponsibilityBurdenGeometry Population Aggregate Contribution Burden) : Set where
  constructor aggregateResponsibilityLoss
  field
    left right : Population
    sameAggregate : aggregateObserver geometry left ≡ aggregateObserver geometry right
    differentContribution : contribution geometry left ≡ contribution geometry right → ⊥

record AggregateBurdenLoss
    {Population Aggregate Contribution Burden : Set}
    (geometry : ResponsibilityBurdenGeometry Population Aggregate Contribution Burden) : Set where
  constructor aggregateBurdenLoss
  field
    left right : Population
    sameAggregate : aggregateObserver geometry left ≡ aggregateObserver geometry right
    differentBurden : burden geometry left ≡ burden geometry right → ⊥

open AggregateResponsibilityLoss public
open AggregateBurdenLoss public

responsibilityDoesNotDescendThroughAggregate :
  ∀ {Population Aggregate Contribution Burden : Set}
    {geometry : ResponsibilityBurdenGeometry Population Aggregate Contribution Burden} →
  AggregateResponsibilityLoss geometry →
  Consumer.FactorsThrough
    (aggregateObserver geometry)
    (contribution geometry) → ⊥
responsibilityDoesNotDescendThroughAggregate witness =
  Consumer.nonDescentWitnessBlocksFactorization
    (Consumer.consumerNonDescentWitness
      (AggregateResponsibilityLoss.left witness)
      (AggregateResponsibilityLoss.right witness)
      (AggregateResponsibilityLoss.sameAggregate witness)
      (AggregateResponsibilityLoss.differentContribution witness))

burdenDoesNotDescendThroughAggregate :
  ∀ {Population Aggregate Contribution Burden : Set}
    {geometry : ResponsibilityBurdenGeometry Population Aggregate Contribution Burden} →
  AggregateBurdenLoss geometry →
  Consumer.FactorsThrough
    (aggregateObserver geometry)
    (burden geometry) → ⊥
burdenDoesNotDescendThroughAggregate witness =
  Consumer.nonDescentWitnessBlocksFactorization
    (Consumer.consumerNonDescentWitness
      (AggregateBurdenLoss.left witness)
      (AggregateBurdenLoss.right witness)
      (AggregateBurdenLoss.sameAggregate witness)
      (AggregateBurdenLoss.differentBurden witness))

------------------------------------------------------------------------
-- Finite asymmetry witness: equal aggregate code, opposite contribution/burden.
------------------------------------------------------------------------

data DemoPopulation : Set where lowerContributionHigherBurden higherContributionLowerBurden : DemoPopulation

data DemoAggregate : Set where sameGlobalOvershoot : DemoAggregate

data DemoContribution : Set where lowContribution highContribution : DemoContribution

data DemoBurden : Set where lowBurden highBurden : DemoBurden

demoAggregate : DemoPopulation → DemoAggregate
demoAggregate _ = sameGlobalOvershoot

demoContribution : DemoPopulation → DemoContribution
demoContribution lowerContributionHigherBurden = lowContribution
demoContribution higherContributionLowerBurden = highContribution

demoBurden : DemoPopulation → DemoBurden
demoBurden lowerContributionHigherBurden = highBurden
demoBurden higherContributionLowerBurden = lowBurden

demoGeometry : ResponsibilityBurdenGeometry DemoPopulation DemoAggregate DemoContribution DemoBurden
demoGeometry = responsibilityBurdenGeometry demoAggregate demoContribution demoBurden

demoResponsibilityLoss : AggregateResponsibilityLoss demoGeometry
demoResponsibilityLoss =
  aggregateResponsibilityLoss lowerContributionHigherBurden higherContributionLowerBurden refl (λ ())

demoBurdenLoss : AggregateBurdenLoss demoGeometry
demoBurdenLoss =
  aggregateBurdenLoss lowerContributionHigherBurden higherContributionLowerBurden refl (λ ())

record ResponsibilityBurdenBoundary : Set where
  constructor responsibilityBurdenBoundary
  field
    aggregateOvershootDeterminesResponsibilityDistribution : Bool
    aggregateOvershootDeterminesResponsibilityDistributionIsFalse :
      aggregateOvershootDeterminesResponsibilityDistribution ≡ false
    aggregateOvershootDeterminesBurdenDistribution : Bool
    aggregateOvershootDeterminesBurdenDistributionIsFalse :
      aggregateOvershootDeterminesBurdenDistribution ≡ false
    contributionEqualsBurden : Bool
    contributionEqualsBurdenIsFalse : contributionEqualsBurden ≡ false

canonicalResponsibilityBurdenBoundary : ResponsibilityBurdenBoundary
canonicalResponsibilityBurdenBoundary =
  responsibilityBurdenBoundary false refl false refl false refl
