module DASHI.Core.ConsumerFamilyRefinementKernelExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF

------------------------------------------------------------------------
-- CONSUMER-FAMILY REFINEMENT KERNEL
--
-- This is a thin indexed adapter over IntersectionalNonFactorability.
-- A consumer family may contain several queries/outcomes.  A collision for one
-- member creates a local refinement obligation.  A valid repair must retain the
-- old observer and additionally pay the failed consumer, but that local repair
-- does not automatically establish adequacy for the whole family.
------------------------------------------------------------------------

record ConsumerFamily (State Index : Set) : Set₁ where
  constructor consumer-family
  field
    Outcome : Index → Set
    observe : (index : Index) → State → Outcome index

open ConsumerFamily public

record FamilyFactorsThrough
    {State Code Index : Set}
    (encode : State → Code)
    (family : ConsumerFamily State Index) : Set₁ where
  constructor family-factors-through
  field
    interpret : (index : Index) → Code → Outcome family index
    factorisation :
      (index : Index) →
      (state : State) →
      observe family index state ≡ interpret index (encode state)

open FamilyFactorsThrough public

consumerFactor :
  ∀ {State Code Index}
    {encode : State → Code}
    {family : ConsumerFamily State Index} →
  FamilyFactorsThrough encode family →
  (index : Index) →
  NF.FactorsThrough encode (observe family index)
consumerFactor factors index =
  NF.factorsThrough
    (interpret factors index)
    (factorisation factors index)

record FamilyCollision
    {State Code Index : Set}
    (encode : State → Code)
    (family : ConsumerFamily State Index) : Set₁ where
  constructor family-collision
  field
    failedConsumer : Index
    witness :
      NF.NonFactorabilityWitness
        encode
        (observe family failedConsumer)

open FamilyCollision public

collisionRulesOutFamilyFactorisation :
  ∀ {State Code Index}
    {encode : State → Code}
    {family : ConsumerFamily State Index} →
  FamilyCollision encode family →
  FamilyFactorsThrough encode family →
  ⊥
collisionRulesOutFamilyFactorisation collision factors =
  NF.witnessRulesOutEveryFlatFactorisation
    (witness collision)
    (consumerFactor factors (failedConsumer collision))

familyRechartCannotRecoverCollision :
  ∀ {State Code Recharted Index}
    {encode : State → Code}
    {family : ConsumerFamily State Index} →
  (rechart : Code → Recharted) →
  (collision : FamilyCollision encode family) →
  FamilyFactorsThrough
    (λ state → rechart (encode state))
    family →
  ⊥
familyRechartCannotRecoverCollision rechart collision factors =
  NF.rechartingCannotRecoverErasedPhenomenon
    rechart
    (witness collision)
    (consumerFactor factors (failedConsumer collision))

record ConsumerRefinementObligation
    {State Code Index : Set}
    (encode : State → Code)
    (family : ConsumerFamily State Index) : Set₁ where
  constructor consumer-refinement-obligation
  field
    collision : FamilyCollision encode family

open ConsumerRefinementObligation public

collisionCreatesRefinementObligation :
  ∀ {State Code Index}
    {encode : State → Code}
    {family : ConsumerFamily State Index} →
  FamilyCollision encode family →
  ConsumerRefinementObligation encode family
collisionCreatesRefinementObligation = consumer-refinement-obligation

record ConsumerFamilyRepair
    {State Coarse Index : Set}
    (coarse : State → Coarse)
    (family : ConsumerFamily State Index)
    (failed : FamilyCollision coarse family) : Set₁ where
  constructor consumer-family-repair
  field
    Refined : Set
    refine : State → Refined
    retainCoarseObserver : NF.FactorsThrough refine coarse
    payFailedConsumer :
      NF.FactorsThrough
        refine
        (observe family (failedConsumer failed))

open ConsumerFamilyRepair public

repairRetainsCoarseObserver :
  ∀ {State Coarse Index}
    {coarse : State → Coarse}
    {family : ConsumerFamily State Index}
    {failed : FamilyCollision coarse family} →
  (repair : ConsumerFamilyRepair coarse family failed) →
  NF.FactorsThrough (refine repair) coarse
repairRetainsCoarseObserver = retainCoarseObserver

repairPaysFailedConsumer :
  ∀ {State Coarse Index}
    {coarse : State → Coarse}
    {family : ConsumerFamily State Index}
    {failed : FamilyCollision coarse family} →
  (repair : ConsumerFamilyRepair coarse family failed) →
  NF.FactorsThrough
    (refine repair)
    (observe family (failedConsumer failed))
repairPaysFailedConsumer = payFailedConsumer

------------------------------------------------------------------------
-- Promotion firewall: repairing the witnessed member is local evidence only.
------------------------------------------------------------------------

data OneConsumerRepairImpliesWholeFamilyAdequacy : Set where

oneConsumerRepairCannotAutoPromoteWholeFamily :
  OneConsumerRepairImpliesWholeFamilyAdequacy → ⊥
oneConsumerRepairCannotAutoPromoteWholeFamily ()
