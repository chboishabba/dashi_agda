module DASHI.Environment.FunctionalEcology where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Environment.LatentDepthFormalism as Latent

------------------------------------------------------------------------
-- Ecological interpretation layer.
--
-- Functional groups are first-class and species are optional refinements.
-- Interaction signs are the canonical SSP trit carrier: negative, neutral,
-- positive.  This types the graph grammar; it does not assert that a sign is
-- context-free, universally measured, or sufficient for ecological authority.

Effect : Set
Effect = SSP.SSPTrit

data FunctionalRole : Set where
  producer : FunctionalRole
  nitrogenFixer : FunctionalRole
  nutrientScavenger : FunctionalRole
  deepRootedEngineer : FunctionalRole
  shallowRootedCover : FunctionalRole
  riparianStabiliser : FunctionalRole
  pollinator : FunctionalRole
  predator : FunctionalRole
  grazer : FunctionalRole
  decomposer : FunctionalRole
  soilEngineer : FunctionalRole
  aquaticFilter : FunctionalRole
  habitatProvider : FunctionalRole
  pathogen : FunctionalRole

record FunctionalGroup : Set where
  constructor mkFunctionalGroup
  field
    groupName : String
    roles : List FunctionalRole
open FunctionalGroup public

data FungalGuild : Set where
  arbuscularMycorrhizal : FungalGuild
  ectomycorrhizal : FungalGuild
  ericoidMycorrhizal : FungalGuild
  saprotrophic : FungalGuild
  endophytic : FungalGuild
  pathogenicFungal : FungalGuild

record ContextGate : Set where
  constructor mkContextGate
  field
    climateCompatible : Bool
    soilCompatible : Bool
    hydrologyCompatible : Bool
    managementCompatible : Bool
    spatiallyConnected : Bool
    seasonallyOverlapping : Bool
open ContextGate public

allContextGatesOpen : ContextGate → Bool
allContextGatesOpen g with climateCompatible g
... | false = false
... | true with soilCompatible g
...   | false = false
...   | true with hydrologyCompatible g
...     | false = false
...     | true with managementCompatible g
...       | false = false
...       | true with spatiallyConnected g
...         | false = false
...         | true = seasonallyOverlapping g

record Interaction : Set where
  constructor mkInteraction
  field
    source : FunctionalGroup
    target : FunctionalGroup
    sign : Effect
    context : ContextGate
    confidenceDepth : Nat
    evidenceLabel : String
open Interaction public

record Guild : Set where
  constructor mkGuild
  field
    guildName : String
    members : List FunctionalGroup
    interactions : List Interaction
    intendedServices : List String
    knownTradeoffs : List String
open Guild public

record SpeciesRefinement : Set where
  constructor mkSpeciesRefinement
  field
    speciesName : String
    functionalProjection : List FunctionalGroup
    habitatNeeds : List String
    threatChannels : List String
    evidenceDepth : Nat
open SpeciesRefinement public

record ThreatenedSpeciesObjective : Set where
  constructor mkThreatenedSpeciesObjective
  field
    focalSpecies : SpeciesRefinement
    desiredSupport : Effect
    supportGroups : List FunctionalGroup
    conflictGroups : List FunctionalGroup
    noNetHarmToNativeGuilds : Bool
open ThreatenedSpeciesObjective public

------------------------------------------------------------------------
-- Intervention grammar for whole-farm and catchment planning.

data InterventionKind : Set where
  planting : InterventionKind
  grazingRegime : InterventionKind
  fungalInoculation : InterventionKind
  soilRemediation : InterventionKind
  contourEarthwork : InterventionKind
  damOrWetland : InterventionKind
  floatingPlanter : InterventionKind
  riparianBuffer : InterventionKind
  habitatCorridor : InterventionKind
  accessTrack : InterventionKind
  irrigation : InterventionKind
  nutrientSourceControl : InterventionKind
  mechanicalRemoval : InterventionKind

record Intervention : Set where
  constructor mkIntervention
  field
    interventionName : String
    kind : InterventionKind
    targetGroups : List FunctionalGroup
    expectedEffects : List Interaction
    activeDepth : Nat
    modelLane : Latent.ModelLane
    reversible : Bool
open Intervention public

record OperationalContext : Set where
  constructor mkOperationalContext
  field
    machineryAvailable : Bool
    machinerySlopeLimitKnown : Bool
    labourAvailable : Bool
    labourCostKnown : Bool
    fuelCostKnown : Bool
    waterCostKnown : Bool
    capitalCostKnown : Bool
    marketPriceKnown : Bool
    legalConstraintsKnown : Bool
    culturalConstraintsRecorded : Bool
open OperationalContext public

record WholeSystemContext : Set₁ where
  constructor mkWholeSystemContext
  field
    GISState : Set
    ClimateState : Set
    SoilState : Set
    WaterState : Set
    EconomyState : Set
    currentGIS : GISState
    currentClimate : ClimateState
    currentSoil : SoilState
    currentWater : WaterState
    currentEconomy : EconomyState
    operations : OperationalContext
open WholeSystemContext public

------------------------------------------------------------------------
-- Mycorrhizal selection is compatibility- and evidence-gated.

record MycorrhizalCandidate : Set where
  constructor mkMycorrhizalCandidate
  field
    fungalGuild : FungalGuild
    hostGroups : List FunctionalGroup
    compatibility : ContextGate
    inoculumProvenanceKnown : Bool
    localBiosecurityCleared : Bool
    fieldEvidenceDepth : Nat
open MycorrhizalCandidate public

mycorrhizalCandidateAdmissible : MycorrhizalCandidate → Bool
mycorrhizalCandidateAdmissible c with allContextGatesOpen (compatibility c)
... | false = false
... | true with inoculumProvenanceKnown c
...   | false = false
...   | true = localBiosecurityCleared c

------------------------------------------------------------------------
-- Explicit non-promotion boundary.

record FunctionalEcologyBoundary : Set where
  constructor mkFunctionalEcologyBoundary
  field
    signIsContextDependent : Bool
    guildIsTemplateNotUniversalRecipe : Bool
    speciesProjectionMayLoseInformation : Bool
    fungalRecommendationRequiresLocalEvidence : Bool
    threatenedSpeciesPlanningRequiresNoNetHarmCheck : Bool
    learnedEffectIsNotCausalProof : Bool
open FunctionalEcologyBoundary public

canonicalFunctionalEcologyBoundary : FunctionalEcologyBoundary
canonicalFunctionalEcologyBoundary =
  mkFunctionalEcologyBoundary true true true true true true

functionalEcologySummary : String
functionalEcologySummary =
  "Ecology is represented as context-gated effects among functional groups and guilds, with optional species refinement, explicit fungal guilds, whole-system interventions, and hard non-promotion boundaries for causality, biosecurity, and threatened-species harm."
