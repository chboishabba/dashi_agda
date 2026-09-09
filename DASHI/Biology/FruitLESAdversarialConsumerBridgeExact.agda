module DASHI.Biology.FruitLESAdversarialConsumerBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Biology.FruitIntegrityAdversarialFibreExact as Fruit
import DASHI.Environment.LESResearchCrossPollinationExact as LES
import DASHI.Biology.Ecology.EcologicalInteractionDynamics as Ecology

------------------------------------------------------------------------
-- FRUIT x LES: SITUATED, TASK-RELATIVE ADVERSARIAL FIBRES
--
-- LES already owns the generic rule that a representation is sufficient only
-- relative to a declared task (`TaskFactorisation`).  We therefore do not
-- create a new fruit-specific compression semantics.  The fruit surface is a
-- candidate representation of a richer ecological/reproductive state.
------------------------------------------------------------------------

data EcologicalRole : Set where
  hostPlant pestConsumer seedDisperser : EcologicalRole

data RoleOutcome : Set where
  favourable neutral adverse : RoleOutcome

data DispersalRelation : Set where
  noDispersalService dispersalServiceDelivered : DispersalRelation

data PestReward : Set where
  noPestReward pestRewardObtained : PestReward

record FruitEcologicalState : Set where
  constructor fruit-ecological-state
  field
    fruitHistory : Fruit.FruitHistory
    pestReward : PestReward
    dispersalRelation : DispersalRelation

open FruitEcologicalState public

surfaceRepresentation : FruitEcologicalState → Fruit.SurfaceIntegrity
surfaceRepresentation state = Fruit.surfaceObserver (fruitHistory state)

roleOutcome : EcologicalRole → FruitEcologicalState → RoleOutcome
roleOutcome hostPlant state with Fruit.seedProtection (fruitHistory state)
... | Fruit.seedProtected = favourable
... | Fruit.seedCompromised = adverse
roleOutcome pestConsumer state with pestReward state
... | noPestReward = adverse
... | pestRewardObtained = favourable
roleOutcome seedDisperser state with dispersalRelation state
... | noDispersalService = neutral
... | dispersalServiceDelivered = favourable

------------------------------------------------------------------------
-- Canonical adversarial states.
------------------------------------------------------------------------

hostIntactNoPest : FruitEcologicalState
hostIntactNoPest =
  fruit-ecological-state
    Fruit.intactProtected
    noPestReward
    noDispersalService

concealedPestExploit : FruitEcologicalState
concealedPestExploit =
  fruit-ecological-state
    Fruit.concealedCompromised
    pestRewardObtained
    noDispersalService

partialLegitimateConsumption : FruitEcologicalState
partialLegitimateConsumption =
  fruit-ecological-state
    Fruit.partiallyEatenProtected
    noPestReward
    dispersalServiceDelivered

partialPestExploit : FruitEcologicalState
partialPestExploit =
  fruit-ecological-state
    Fruit.partiallyEatenCompromised
    pestRewardObtained
    noDispersalService

------------------------------------------------------------------------
-- Same surface, opposite task consequences.
------------------------------------------------------------------------

concealedExploitSameSurface :
  surfaceRepresentation hostIntactNoPest ≡
  surfaceRepresentation concealedPestExploit
concealedExploitSameSurface = refl

partialConsumptionSameSurface :
  surfaceRepresentation partialLegitimateConsumption ≡
  surfaceRepresentation partialPestExploit
partialConsumptionSameSurface = refl

concealedExploitChangesHostOutcome :
  roleOutcome hostPlant hostIntactNoPest ≡
  roleOutcome hostPlant concealedPestExploit →
  ⊥
concealedExploitChangesHostOutcome ()

concealedExploitChangesPestOutcome :
  roleOutcome pestConsumer hostIntactNoPest ≡
  roleOutcome pestConsumer concealedPestExploit →
  ⊥
concealedExploitChangesPestOutcome ()

partialConsumptionChangesHostOutcome :
  roleOutcome hostPlant partialLegitimateConsumption ≡
  roleOutcome hostPlant partialPestExploit →
  ⊥
partialConsumptionChangesHostOutcome ()

partialConsumptionChangesDisperserOutcome :
  roleOutcome seedDisperser partialLegitimateConsumption ≡
  roleOutcome seedDisperser partialPestExploit →
  ⊥
partialConsumptionChangesDisperserOutcome ()

------------------------------------------------------------------------
-- LES task-factorisation no-go.
--
-- If the surface alone admitted a LES TaskFactorisation for all ecological
-- roles, same surface would force same role outcome.  The concrete exploit
-- collisions refute that.
------------------------------------------------------------------------

surfaceCannotFactorAllRoleOutcomes :
  LES.TaskFactorisation surfaceRepresentation roleOutcome → ⊥
surfaceCannotFactorAllRoleOutcomes factor =
  concealedExploitChangesHostOutcome
    (LES.sameRepresentationSameTaskOutput
      factor
      hostPlant
      concealedExploitSameSurface)

surfaceCannotFactorPestOutcomeEither :
  LES.TaskFactorisation surfaceRepresentation roleOutcome → ⊥
surfaceCannotFactorPestOutcomeEither factor =
  concealedExploitChangesPestOutcome
    (LES.sameRepresentationSameTaskOutput
      factor
      pestConsumer
      concealedExploitSameSurface)

surfaceCannotFactorPartialConsumptionConsequences :
  LES.TaskFactorisation surfaceRepresentation roleOutcome → ⊥
surfaceCannotFactorPartialConsumptionConsequences factor =
  partialConsumptionChangesHostOutcome
    (LES.sameRepresentationSameTaskOutput
      factor
      hostPlant
      partialConsumptionSameSurface)

------------------------------------------------------------------------
-- Exploit transition semantics.
--
-- An exploit is not merely damage.  It is a transition on one carrier where
-- the attacker outcome improves while the host outcome worsens.  Surface
-- invisibility is an additional property, not part of the definition.
------------------------------------------------------------------------

record AdversarialExploitTransition : Set where
  constructor adversarial-exploit-transition
  field
    before after : FruitEcologicalState
    attacker : EcologicalRole
    host : EcologicalRole
    attackerBefore : roleOutcome attacker before ≡ adverse
    attackerAfter : roleOutcome attacker after ≡ favourable
    hostBefore : roleOutcome host before ≡ favourable
    hostAfter : roleOutcome host after ≡ adverse

open AdversarialExploitTransition public

canonicalConcealedPestExploit : AdversarialExploitTransition
canonicalConcealedPestExploit =
  adversarial-exploit-transition
    hostIntactNoPest
    concealedPestExploit
    pestConsumer
    hostPlant
    refl refl refl refl

record ObserverInvisibleExploit
    (exploit : AdversarialExploitTransition) : Set where
  constructor observer-invisible-exploit
  field
    sameSurface :
      surfaceRepresentation (before exploit) ≡
      surfaceRepresentation (after exploit)

open ObserverInvisibleExploit public

canonicalConcealedPestExploitIsSurfaceInvisible :
  ObserverInvisibleExploit canonicalConcealedPestExploit
canonicalConcealedPestExploitIsSurfaceInvisible =
  observer-invisible-exploit refl

------------------------------------------------------------------------
-- Adapter seam into the existing ecological world owner.
--
-- LES / EcologicalInteractionDynamics remains owner of world evolution.  This
-- bridge only requires a caller to identify the fruit carrier and exploit
-- transition with one existing EcologicalSystem interaction; it does not add a
-- second ecosystem step function.
------------------------------------------------------------------------

record FruitExploitEcologyAdapter
    (E : Ecology.EcologicalSystem) : Set₁ where
  open Ecology.EcologicalSystem E
  field
    encodeFruitState : FruitEcologicalState → EcosystemState
    pestInteraction : Interaction
    exploitRealised :
      interact pestInteraction (encodeFruitState hostIntactNoPest) ≡
      encodeFruitState concealedPestExploit

open FruitExploitEcologyAdapter public

------------------------------------------------------------------------
-- LES / ecological firewalls.
------------------------------------------------------------------------

data SameSurfaceMeansSameEcologicalTaskOutcomePermission : Set where

data PestBenefitMeansHostDamagePermission : Set where

data ExploitMeansObserverInvisiblePermission : Set where

data OneExploitMeansEvolutionaryFixationPermission : Set where

sameSurfaceDoesNotMeanSameEcologicalTaskOutcome :
  SameSurfaceMeansSameEcologicalTaskOutcomePermission → ⊥
sameSurfaceDoesNotMeanSameEcologicalTaskOutcome ()

pestBenefitDoesNotByItselfMeanHostDamage :
  PestBenefitMeansHostDamagePermission → ⊥
pestBenefitDoesNotByItselfMeanHostDamage ()

exploitNeedNotBeObserverInvisible :
  ExploitMeansObserverInvisiblePermission → ⊥
exploitNeedNotBeObserverInvisible ()

oneExploitDoesNotProveEvolutionaryFixation :
  OneExploitMeansEvolutionaryFixationPermission → ⊥
oneExploitDoesNotProveEvolutionaryFixation ()

record FruitLESAdversarialBoundary : Set where
  constructor fruit-les-adversarial-boundary
  field
    surfaceCompressionIsTaskRelative : Bool
    sameSurfaceMayChangeHostOutcome : Bool
    sameSurfaceMayChangePestOutcome : Bool
    partialEatingMaySeparateLegitimateAndExploitConsumption : Bool
    exploitIsRoleRelativeTransitionOnOneCarrier : Bool
    observerInvisibilityIsSeparateExploitProperty : Bool
    ecologyWorldStepHasExistingOwner : Bool
    oneExploitAutomaticallyMeansEvolutionaryFixation : Bool

canonicalFruitLESAdversarialBoundary : FruitLESAdversarialBoundary
canonicalFruitLESAdversarialBoundary =
  fruit-les-adversarial-boundary
    true true true true true true true false
