module DASHI.Environment.BiocontrolCostedExperimentChoiceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice
import DASHI.Core.DiscriminatorSynthesisExact as Synthesis
import DASHI.Environment.BiocontrolExternalityExperimentExact as Experiment

------------------------------------------------------------------------
-- Declared experiment library.
--
-- The Nat costs below are synthetic search/resource ranks for the finite
-- fixture. They are not dollars, welfare weights, empirical effort estimates,
-- experimental ethics, or deployment authority.
------------------------------------------------------------------------

nutrientSeedbankBundle : Synthesis.ExperimentBundle Experiment.InterventionWorld
nutrientSeedbankBundle = Synthesis.experimentBundle
  (Experiment.NutrientResidual × Experiment.SeedbankResidual)
  (λ world → Experiment.nutrientResidual world , Experiment.seedbankResidual world)
  1
  "nutrient plus seedbank residual probe"
  "LES nutrient-conservation plus seedbank observation contracts"

oxygenBiomassFateBundle : Synthesis.ExperimentBundle Experiment.InterventionWorld
oxygenBiomassFateBundle = Synthesis.experimentBundle
  (Experiment.OxygenState × Experiment.BiomassFate)
  (λ world → Experiment.oxygen world , Experiment.biomassFate world)
  2
  "dissolved-oxygen plus biomass-fate probe"
  "declared dissolved-oxygen measurement plus export-versus-in-situ biomass-fate observation"

communityCompositionBundle : Synthesis.ExperimentBundle Experiment.InterventionWorld
communityCompositionBundle = Synthesis.experimentBundle
  Experiment.CommunityState
  Experiment.community
  3
  "replacement-community composition probe"
  "declared community-composition survey"

agentInteractionBundle : Synthesis.ExperimentBundle Experiment.InterventionWorld
agentInteractionBundle = Synthesis.experimentBundle
  Experiment.AgentInteraction
  Experiment.interaction
  4
  "biocontrol-agent interaction probe"
  "declared agent-density, damage, abiotic-context and co-occurrence observation"

nutrientMove oxygenMove communityMove interactionMove : Choice.InformationMove
nutrientMove = Synthesis.bundleInformationMove nutrientSeedbankBundle
oxygenMove = Synthesis.bundleInformationMove oxygenBiomassFateBundle
communityMove = Synthesis.bundleInformationMove communityCompositionBundle
interactionMove = Synthesis.bundleInformationMove agentInteractionBundle

------------------------------------------------------------------------
-- The declared comparison set is finite and explicit.
------------------------------------------------------------------------

data DeclaredMove : Choice.InformationMove → Set where
  nutrientDeclared : DeclaredMove nutrientMove
  oxygenDeclared : DeclaredMove oxygenMove
  communityDeclared : DeclaredMove communityMove
  interactionDeclared : DeclaredMove interactionMove

------------------------------------------------------------------------
-- Consumer-specific obstructions and resolution languages.
-- A low-cost probe for one consumer does not thereby resolve another consumer.
------------------------------------------------------------------------

data OxygenObstruction : Set where oxygenUnresolved : OxygenObstruction
data NutrientObstruction : Set where nutrientReboundUnresolved : NutrientObstruction
data CommunityObstruction : Set where restorationUnresolved : CommunityObstruction
data InteractionObstruction : Set where agentInteractionUnresolved : InteractionObstruction

data ResolvesOxygen : Choice.InformationMove → OxygenObstruction → Set where
  oxygenProbeResolves : ResolvesOxygen oxygenMove oxygenUnresolved

data ResolvesNutrient : Choice.InformationMove → NutrientObstruction → Set where
  nutrientProbeResolves : ResolvesNutrient nutrientMove nutrientReboundUnresolved

data ResolvesCommunity : Choice.InformationMove → CommunityObstruction → Set where
  communityProbeResolves : ResolvesCommunity communityMove restorationUnresolved

data ResolvesInteraction : Choice.InformationMove → InteractionObstruction → Set where
  interactionProbeResolves : ResolvesInteraction interactionMove agentInteractionUnresolved

oxygenProblem nutrientProblem communityProblem interactionProblem : Choice.ActionabilityProblem
oxygenProblem = Choice.actionabilityProblem
  OxygenObstruction oxygenUnresolved ResolvesOxygen
  "suppression-equivalent worlds remain oxygen-distinct"
  "dissolved-oxygen outcome consumer"
  "measurement resolution does not itself authorise intervention"

nutrientProblem = Choice.actionabilityProblem
  NutrientObstruction nutrientReboundUnresolved ResolvesNutrient
  "present suppression does not close nutrient/seedbank rebound risk"
  "future reinvasion/rebound consumer"
  "measurement resolution does not itself authorise intervention"

communityProblem = Choice.actionabilityProblem
  CommunityObstruction restorationUnresolved ResolvesCommunity
  "suppression plus present oxygen does not close restoration outcome"
  "replacement-community restoration consumer"
  "measurement resolution does not itself authorise intervention"

interactionProblem = Choice.actionabilityProblem
  InteractionObstruction agentInteractionUnresolved ResolvesInteraction
  "agent count does not determine interaction outcome"
  "biocontrol-agent interaction consumer"
  "measurement resolution does not itself authorise intervention"

------------------------------------------------------------------------
-- Cheapest resolving moves. Minimality is only among the explicitly declared
-- alternatives that actually resolve the corresponding consumer obstruction.
------------------------------------------------------------------------

canonicalCheapestOxygen : Choice.CheapestResolvingMove oxygenProblem DeclaredMove
canonicalCheapestOxygen = Choice.cheapestResolvingMove
  (Choice.resolvingMove oxygenMove oxygenProbeResolves)
  oxygenDeclared
  (λ alternative declared resolves → helper alternative resolves)
  "oxygen/biomass-fate bundle is minimal among declared moves that resolve the oxygen obstruction"
  where
    helper : (alternative : Choice.InformationMove) →
      ResolvesOxygen alternative oxygenUnresolved →
      Choice.cost oxygenMove ≤ Choice.cost alternative
    helper .oxygenMove oxygenProbeResolves = ≤-refl

canonicalCheapestNutrient : Choice.CheapestResolvingMove nutrientProblem DeclaredMove
canonicalCheapestNutrient = Choice.cheapestResolvingMove
  (Choice.resolvingMove nutrientMove nutrientProbeResolves)
  nutrientDeclared
  (λ alternative declared resolves → helper alternative resolves)
  "nutrient/seedbank bundle is minimal among declared moves that resolve the rebound obstruction"
  where
    helper : (alternative : Choice.InformationMove) →
      ResolvesNutrient alternative nutrientReboundUnresolved →
      Choice.cost nutrientMove ≤ Choice.cost alternative
    helper .nutrientMove nutrientProbeResolves = ≤-refl

canonicalCheapestCommunity : Choice.CheapestResolvingMove communityProblem DeclaredMove
canonicalCheapestCommunity = Choice.cheapestResolvingMove
  (Choice.resolvingMove communityMove communityProbeResolves)
  communityDeclared
  (λ alternative declared resolves → helper alternative resolves)
  "community-composition bundle is minimal among declared moves that resolve the restoration obstruction"
  where
    helper : (alternative : Choice.InformationMove) →
      ResolvesCommunity alternative restorationUnresolved →
      Choice.cost communityMove ≤ Choice.cost alternative
    helper .communityMove communityProbeResolves = ≤-refl

canonicalCheapestInteraction : Choice.CheapestResolvingMove interactionProblem DeclaredMove
canonicalCheapestInteraction = Choice.cheapestResolvingMove
  (Choice.resolvingMove interactionMove interactionProbeResolves)
  interactionDeclared
  (λ alternative declared resolves → helper alternative resolves)
  "agent-interaction bundle is minimal among declared moves that resolve the interaction obstruction"
  where
    helper : (alternative : Choice.InformationMove) →
      ResolvesInteraction alternative agentInteractionUnresolved →
      Choice.cost interactionMove ≤ Choice.cost alternative
    helper .interactionMove interactionProbeResolves = ≤-refl

------------------------------------------------------------------------
-- Concrete collision -> separating bundle witnesses.
------------------------------------------------------------------------

oxygenBundleSeparatesCollision :
  Synthesis.BundleSeparates
    oxygenBiomassFateBundle Experiment.oxygenDebtWorld Experiment.oxygenRecoveryWorld
oxygenBundleSeparatesCollision = Synthesis.bundleSeparates (λ ())

reboundBundleSeparatesCollision :
  Synthesis.BundleSeparates
    nutrientSeedbankBundle Experiment.reboundHighWorld Experiment.reboundLowWorld
reboundBundleSeparatesCollision = Synthesis.bundleSeparates (λ ())

communityBundleSeparatesCollision :
  Synthesis.BundleSeparates
    communityCompositionBundle
    Experiment.restorationFailureWorld Experiment.restorationRecoveryWorld
communityBundleSeparatesCollision = Synthesis.bundleSeparates (λ ())

agentBundleSeparatesCollision :
  Synthesis.BundleSeparates
    agentInteractionBundle
    Experiment.agentIndependentWorld Experiment.agentInterferenceWorld
agentBundleSeparatesCollision = Synthesis.bundleSeparates (λ ())

------------------------------------------------------------------------
-- Regression-facing receipts and cross-consumer firewall.
------------------------------------------------------------------------

record OxygenChoiceReceipt : Set₁ where
  constructor oxygenChoiceReceipt
  field choice : Choice.CheapestResolvingMove oxygenProblem DeclaredMove
record NutrientChoiceReceipt : Set₁ where
  constructor nutrientChoiceReceipt
  field choice : Choice.CheapestResolvingMove nutrientProblem DeclaredMove
record CommunityChoiceReceipt : Set₁ where
  constructor communityChoiceReceipt
  field choice : Choice.CheapestResolvingMove communityProblem DeclaredMove
record AgentInteractionChoiceReceipt : Set₁ where
  constructor agentInteractionChoiceReceipt
  field choice : Choice.CheapestResolvingMove interactionProblem DeclaredMove

canonicalOxygenChoice : OxygenChoiceReceipt
canonicalOxygenChoice = oxygenChoiceReceipt canonicalCheapestOxygen
canonicalNutrientChoice : NutrientChoiceReceipt
canonicalNutrientChoice = nutrientChoiceReceipt canonicalCheapestNutrient
canonicalCommunityChoice : CommunityChoiceReceipt
canonicalCommunityChoice = communityChoiceReceipt canonicalCheapestCommunity
canonicalAgentInteractionChoice : AgentInteractionChoiceReceipt
canonicalAgentInteractionChoice = agentInteractionChoiceReceipt canonicalCheapestInteraction

record OxygenCollisionBackedChoiceReceipt : Set₁ where
  constructor oxygenCollisionBackedChoiceReceipt
  field
    collision : Experiment.OxygenCollisionReceipt
    separator :
      Synthesis.BundleSeparates
        oxygenBiomassFateBundle Experiment.oxygenDebtWorld Experiment.oxygenRecoveryWorld
    cheapestResolving : Choice.CheapestResolvingMove oxygenProblem DeclaredMove

canonicalOxygenCollisionBackedChoice : OxygenCollisionBackedChoiceReceipt
canonicalOxygenCollisionBackedChoice = oxygenCollisionBackedChoiceReceipt
  Experiment.canonicalOxygenCollision
  oxygenBundleSeparatesCollision
  canonicalCheapestOxygen

record ReboundCollisionBackedChoiceReceipt : Set₁ where
  constructor reboundCollisionBackedChoiceReceipt
  field
    collision : Experiment.ReboundCollisionReceipt
    separator :
      Synthesis.BundleSeparates
        nutrientSeedbankBundle Experiment.reboundHighWorld Experiment.reboundLowWorld
    cheapestResolving : Choice.CheapestResolvingMove nutrientProblem DeclaredMove

canonicalReboundCollisionBackedChoice : ReboundCollisionBackedChoiceReceipt
canonicalReboundCollisionBackedChoice = reboundCollisionBackedChoiceReceipt
  Experiment.canonicalReboundCollision
  reboundBundleSeparatesCollision
  canonicalCheapestNutrient

record RestorationCollisionBackedChoiceReceipt : Set₁ where
  constructor restorationCollisionBackedChoiceReceipt
  field
    collision : Experiment.RestorationCollisionReceipt
    separator :
      Synthesis.BundleSeparates
        communityCompositionBundle
        Experiment.restorationFailureWorld Experiment.restorationRecoveryWorld
    cheapestResolving : Choice.CheapestResolvingMove communityProblem DeclaredMove

canonicalRestorationCollisionBackedChoice : RestorationCollisionBackedChoiceReceipt
canonicalRestorationCollisionBackedChoice = restorationCollisionBackedChoiceReceipt
  Experiment.canonicalRestorationCollision
  communityBundleSeparatesCollision
  canonicalCheapestCommunity

record AgentCollisionBackedChoiceReceipt : Set₁ where
  constructor agentCollisionBackedChoiceReceipt
  field
    collision : Experiment.AgentInteractionCollisionReceipt
    separator :
      Synthesis.BundleSeparates
        agentInteractionBundle
        Experiment.agentIndependentWorld Experiment.agentInterferenceWorld
    cheapestResolving : Choice.CheapestResolvingMove interactionProblem DeclaredMove

canonicalAgentCollisionBackedChoice : AgentCollisionBackedChoiceReceipt
canonicalAgentCollisionBackedChoice = agentCollisionBackedChoiceReceipt
  Experiment.canonicalAgentInteractionCollision
  agentBundleSeparatesCollision
  canonicalCheapestInteraction

cheaperNutrientProbeDoesNotResolveOxygen :
  Choice.Resolves oxygenProblem nutrientMove (Choice.currentObstruction oxygenProblem) → ⊥
cheaperNutrientProbeDoesNotResolveOxygen ()

record CrossConsumerCostBoundary : Set where
  constructor crossConsumerCostBoundary
  field
    cheapestDeclaredMoveNeedNotResolveEveryConsumer : Bool
    cheapestDeclaredMoveNeedNotResolveEveryConsumerIsTrue :
      cheapestDeclaredMoveNeedNotResolveEveryConsumer ≡ true
    declaredCostIsEmpiricalMoney : Bool
    declaredCostIsEmpiricalMoneyIsFalse : declaredCostIsEmpiricalMoney ≡ false
    leastCostResolutionCreatesDeploymentAuthority : Bool
    leastCostResolutionCreatesDeploymentAuthorityIsFalse :
      leastCostResolutionCreatesDeploymentAuthority ≡ false
    abstractObstructionMayIgnoreConcreteCollision : Bool
    abstractObstructionMayIgnoreConcreteCollisionIsFalse :
      abstractObstructionMayIgnoreConcreteCollision ≡ false

canonicalCrossConsumerCostBoundary : CrossConsumerCostBoundary
canonicalCrossConsumerCostBoundary =
  crossConsumerCostBoundary true refl false refl false refl false refl
