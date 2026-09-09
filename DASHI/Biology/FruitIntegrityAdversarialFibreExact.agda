module DASHI.Biology.FruitIntegrityAdversarialFibreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Consumer

------------------------------------------------------------------------
-- FRUIT INTEGRITY AS A CONSUMER-INDEXED OBSERVATION FIBRE
--
-- This is deliberately not a cryptographic-hash claim.  A fruit surface is an
-- observer of a richer reproductive history.  Different hidden histories may
-- lie in the same observer fibre while mattering differently to a declared
-- downstream consumer such as seed protection.
--
-- In particular, partial consumption is not identified with reproductive
-- failure: a visibly partially eaten fruit may still protect its seeds, while
-- another equally partially eaten fruit may have compromised them.
------------------------------------------------------------------------

data SurfaceIntegrity : Set where
  apparentlyIntact visiblyPartiallyEaten : SurfaceIntegrity

data SeedProtection : Set where
  seedProtected seedCompromised : SeedProtection

data ConsumptionRelation : Set where
  noConsumption
  partialConsumptionWithSeedProtection
  partialConsumptionWithSeedCompromise
  concealedInternalExploit : ConsumptionRelation

record FruitHistory : Set where
  constructor fruit-history
  field
    surface : SurfaceIntegrity
    seedProtection : SeedProtection
    consumptionRelation : ConsumptionRelation

open FruitHistory public

------------------------------------------------------------------------
-- Canonical finite witnesses.
------------------------------------------------------------------------

intactProtected : FruitHistory
intactProtected =
  fruit-history apparentlyIntact seedProtected noConsumption

partiallyEatenProtected : FruitHistory
partiallyEatenProtected =
  fruit-history
    visiblyPartiallyEaten
    seedProtected
    partialConsumptionWithSeedProtection

partiallyEatenCompromised : FruitHistory
partiallyEatenCompromised =
  fruit-history
    visiblyPartiallyEaten
    seedCompromised
    partialConsumptionWithSeedCompromise

concealedCompromised : FruitHistory
concealedCompromised =
  fruit-history
    apparentlyIntact
    seedCompromised
    concealedInternalExploit

------------------------------------------------------------------------
-- Observers and consumers.
------------------------------------------------------------------------

surfaceObserver : FruitHistory → SurfaceIntegrity
surfaceObserver = surface

seedProtectionConsumer : FruitHistory → SeedProtection
seedProtectionConsumer = seedProtection

consumptionRelationObserver : FruitHistory → ConsumptionRelation
consumptionRelationObserver = consumptionRelation

------------------------------------------------------------------------
-- Fibre collisions.
--
-- 1. Concealed exploit: apparently intact does not imply seed protection.
-- 2. Visible partial eating: "tampered" does not determine whether the
--    reproductive payload was actually compromised.
------------------------------------------------------------------------

apparentlyIntactCollision :
  Consumer.ConsumerNonDescentWitness
    surfaceObserver
    seedProtectionConsumer
apparentlyIntactCollision =
  Consumer.consumerNonDescentWitness
    intactProtected
    concealedCompromised
    refl
    (λ ())

partiallyEatenCollision :
  Consumer.ConsumerNonDescentWitness
    surfaceObserver
    seedProtectionConsumer
partiallyEatenCollision =
  Consumer.consumerNonDescentWitness
    partiallyEatenProtected
    partiallyEatenCompromised
    refl
    (λ ())

surfaceNotSufficientForSeedProtection :
  Consumer.ConsumerSufficient
    surfaceObserver
    seedProtectionConsumer →
  ⊥
surfaceNotSufficientForSeedProtection =
  Consumer.nonDescentWitnessBlocksSufficiency apparentlyIntactCollision

surfaceDoesNotFactorSeedProtection :
  Consumer.FactorsThrough
    surfaceObserver
    seedProtectionConsumer →
  ⊥
surfaceDoesNotFactorSeedProtection =
  Consumer.nonDescentWitnessBlocksFactorization apparentlyIntactCollision

partialEatingSurfaceAlsoFailsSeedProtection :
  Consumer.ConsumerSufficient
    surfaceObserver
    seedProtectionConsumer →
  ⊥
partialEatingSurfaceAlsoFailsSeedProtection =
  Consumer.nonDescentWitnessBlocksSufficiency partiallyEatenCollision

------------------------------------------------------------------------
-- A consumer-indexed repair.
--
-- The consumer itself is always sufficient for that consumer.  This is not a
-- claim that seed protection is a complete biological observer; it is exactly
-- the repository's least-sufficient consumer-observer theorem.
------------------------------------------------------------------------

seedProtectionObserverIsLeastSufficient :
  Consumer.LeastSufficientConsumerObserver seedProtectionConsumer
seedProtectionObserverIsLeastSufficient =
  Consumer.canonicalConsumerObserverIsLeast seedProtectionConsumer

------------------------------------------------------------------------
-- Tamper-evident / tamper-proof firewalls.
------------------------------------------------------------------------

data VisibleDamageMeansSeedCompromisePermission : Set where

data ApparentIntegrityMeansNoAttackPermission : Set where

data PartialConsumptionMeansFailedDispersalPermission : Set where

data FruitSurfaceMeansCryptographicHashPermission : Set where

visibleDamageDoesNotByItselfMeanSeedCompromise :
  VisibleDamageMeansSeedCompromisePermission → ⊥
visibleDamageDoesNotByItselfMeanSeedCompromise ()

apparentIntegrityDoesNotByItselfMeanNoAttack :
  ApparentIntegrityMeansNoAttackPermission → ⊥
apparentIntegrityDoesNotByItselfMeanNoAttack ()

partialConsumptionDoesNotByItselfMeanFailedDispersal :
  PartialConsumptionMeansFailedDispersalPermission → ⊥
partialConsumptionDoesNotByItselfMeanFailedDispersal ()

fruitSurfaceIsNotPromotedToCryptographicHash :
  FruitSurfaceMeansCryptographicHashPermission → ⊥
fruitSurfaceIsNotPromotedToCryptographicHash ()

record FruitIntegrityAdversarialFibreBoundary : Set where
  constructor fruit-integrity-adversarial-fibre-boundary
  field
    fruitSurfaceIsObservationOfRicherHistory : Bool
    apparentlyIntactStatesMayHideDifferentSeedOutcomes : Bool
    partiallyEatenStatesMayHideDifferentSeedOutcomes : Bool
    surfaceObservationIsConsumerSufficientForSeedProtection : Bool
    visibleDamageAutomaticallyMeansSeedCompromise : Bool
    apparentIntegrityAutomaticallyMeansNoAttack : Bool
    partialConsumptionAutomaticallyMeansFailedDispersal : Bool
    fruitSurfaceIsLiteralCryptographicHash : Bool

canonicalFruitIntegrityAdversarialFibreBoundary :
  FruitIntegrityAdversarialFibreBoundary
canonicalFruitIntegrityAdversarialFibreBoundary =
  fruit-integrity-adversarial-fibre-boundary
    true true true false false false false false
