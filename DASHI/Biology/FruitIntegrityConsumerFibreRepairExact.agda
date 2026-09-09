module DASHI.Biology.FruitIntegrityConsumerFibreRepairExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Core.ConsumerFibreRepairExact as Repair
import DASHI.Biology.FruitIntegrityAdversarialFibreExact as Fruit

------------------------------------------------------------------------
-- FRUIT OBSERVER REPAIR = CONSUMER-INDEXED FIBRE SEPARATION
--
-- Reuse the repository-wide repair theorem.  We do not prescribe one global
-- "better fruit hash".  For the declared seed-protection consumer, every
-- sufficient refinement of the surface observer must separate each witnessed
-- collision that changes seed outcome.
------------------------------------------------------------------------

anySeedProtectionRepairMustSeparateConcealedExploit :
  ∀ {Refinement : Set}
    (refine : Fruit.FruitHistory → Refinement) →
  Repair.RefinementRepairs
    Fruit.surfaceObserver
    refine
    Fruit.seedProtectionConsumer →
  refine Fruit.intactProtected ≡ refine Fruit.concealedCompromised →
  ⊥
anySeedProtectionRepairMustSeparateConcealedExploit refine repaired =
  Repair.refinementRepairSeparatesWitness
    Fruit.apparentlyIntactCollision
    repaired

anySeedProtectionRepairMustSeparatePartialEatingOutcomes :
  ∀ {Refinement : Set}
    (refine : Fruit.FruitHistory → Refinement) →
  Repair.RefinementRepairs
    Fruit.surfaceObserver
    refine
    Fruit.seedProtectionConsumer →
  refine Fruit.partiallyEatenProtected ≡
    refine Fruit.partiallyEatenCompromised →
  ⊥
anySeedProtectionRepairMustSeparatePartialEatingOutcomes refine repaired =
  Repair.refinementRepairSeparatesWitness
    Fruit.partiallyEatenCollision
    repaired

------------------------------------------------------------------------
-- The existing consumption-relation coordinate does separate both concrete
-- collisions.  This is only a local separation receipt; by the core theorem's
-- design it is not silently promoted to global sufficiency.
------------------------------------------------------------------------

concealedExploitConsumptionCoordinateSeparates :
  Fruit.consumptionRelationObserver Fruit.intactProtected ≡
  Fruit.consumptionRelationObserver Fruit.concealedCompromised →
  ⊥
concealedExploitConsumptionCoordinateSeparates ()

partialEatingConsumptionCoordinateSeparates :
  Fruit.consumptionRelationObserver Fruit.partiallyEatenProtected ≡
  Fruit.consumptionRelationObserver Fruit.partiallyEatenCompromised →
  ⊥
partialEatingConsumptionCoordinateSeparates ()

------------------------------------------------------------------------
-- Firewalls: one repair coordinate can be useful without becoming a universal
-- integrity oracle or a proof of complete biological state reconstruction.
------------------------------------------------------------------------

data LocalSeparationMeansGlobalSufficiencyPermission : Set where

data SeedProtectionConsumerMeansWorldCompleteFruitOntologyPermission : Set where

localSeparationDoesNotProveGlobalSufficiency :
  LocalSeparationMeansGlobalSufficiencyPermission → ⊥
localSeparationDoesNotProveGlobalSufficiency ()

seedProtectionConsumerIsNotWorldCompleteFruitOntology :
  SeedProtectionConsumerMeansWorldCompleteFruitOntologyPermission → ⊥
seedProtectionConsumerIsNotWorldCompleteFruitOntology ()
