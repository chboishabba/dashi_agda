module DASHI.Reasoning.PathologicTheatreMetaRuntime where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.PathologicConstraintSystem as Constraint

------------------------------------------------------------------------
-- Source calibration:
--
-- * Harris Brewis (hbomberguy), "Pathologic is Genius, And Here's Why",
--   YouTube, 21 November 2019, no DOI.
-- * Alejandro Arévalo Arenas and Alberto Porta Pérez, "Performance in
--   Multiple Realities: Theatrical Resource Inheritance in Pathologic 2",
--   Tecnología y Creatividad Aplicada 1(1), 2025,
--   DOI 10.5281/zenodo.17483228.
-- * Marie Beckmann, "Posthuman tragedy on the virtual stage in Pathologic 2",
--   DOI 10.1080/14794713.2025.2555035.
--
-- Theatre, player, character and developer layers are related by typed edges.
-- A metafictional reveal changes provenance knowledge without erasing the
-- causal or affective trace internal to the enacted run.
------------------------------------------------------------------------

data PerformanceAgent : Set where
  developers player gameSystem children powersThatBe executors : PerformanceAgent
  avatar : Constraint.Doctor → PerformanceAgent

data Controls : PerformanceAgent → PerformanceAgent → Set where
  playerControlsAvatar :
    ∀ {doctor} → Controls player (avatar doctor)
  gameConstrainsPlayer : Controls gameSystem player
  developersAuthorSystem : Controls developers gameSystem
  childrenStageTown : Controls children gameSystem
  developersStageChildren : Controls developers children

data Addresses : PerformanceAgent → PerformanceAgent → Set where
  executorsAddressPlayer : Addresses executors player
  developersAddressPlayer : Addresses developers player
  powersAddressAvatar :
    ∀ {doctor} → Addresses powersThatBe (avatar doctor)

record MutualPlayDependency (doctor : Constraint.Doctor) : Set where
  field
    playerAgency : Controls player (avatar doctor)
    systemCounterAgency : Controls gameSystem player
    authoredConstraint : Controls developers gameSystem
    playerIsSoleUnconditionedController : Bool
    dependencyReceipt : String

open MutualPlayDependency public

canonicalBachelorMutualPlay :
  MutualPlayDependency Constraint.bachelor
canonicalBachelorMutualPlay = record
  { playerAgency = playerControlsAvatar
  ; systemCounterAgency = gameConstrainsPlayer
  ; authoredConstraint = developersAuthorSystem
  ; playerIsSoleUnconditionedController = false
  ; dependencyReceipt =
      "The player selects actions through the Bachelor while time, survival, quest and authored constraints act back on the player."
  }

------------------------------------------------------------------------
-- Performance layers and provenance reveal.
------------------------------------------------------------------------

data PerformanceLayer : Set where
  developerLayer playerLayer theatreLayer characterLayer townLayer childGameLayer : PerformanceLayer

data LayerDependsOn : PerformanceLayer → PerformanceLayer → Set where
  gameDependsOnDevelopers : LayerDependsOn playerLayer developerLayer
  theatreDependsOnPlayer : LayerDependsOn theatreLayer playerLayer
  characterDependsOnTheatre : LayerDependsOn characterLayer theatreLayer
  townDependsOnCharacter : LayerDependsOn townLayer characterLayer
  childGameDependsOnDeveloperFrame : LayerDependsOn childGameLayer developerLayer

record TheatreDependencyChain : Set where
  field
    playerDeveloperDependency : LayerDependsOn playerLayer developerLayer
    theatrePlayerDependency : LayerDependsOn theatreLayer playerLayer
    characterTheatreDependency : LayerDependsOn characterLayer theatreLayer
    townCharacterDependency : LayerDependsOn townLayer characterLayer
    childDeveloperDependency : LayerDependsOn childGameLayer developerLayer
    chainReceipt : String

canonicalTheatreDependencyChain : TheatreDependencyChain
canonicalTheatreDependencyChain = record
  { playerDeveloperDependency = gameDependsOnDevelopers
  ; theatrePlayerDependency = theatreDependsOnPlayer
  ; characterTheatreDependency = characterDependsOnTheatre
  ; townCharacterDependency = townDependsOnCharacter
  ; childDeveloperDependency = childGameDependsOnDeveloperFrame
  ; chainReceipt =
      "The theatre opening, child-game reveal and developer conversation form nested provenance layers rather than one flat ontological switch."
  }

data OntologicalStatus : Set where
  enactedFiction disclosedConstruction : OntologicalStatus

data TraceStatus : Set where
  causalTraceRetained causalTraceErased : TraceStatus

retainedTraceIsNotErased :
  causalTraceRetained ≡ causalTraceErased → ⊥
retainedTraceIsNotErased ()

record MetaReveal : Set where
  field
    beforeStatus : OntologicalStatus
    afterStatus : OntologicalStatus
    traceAfterReveal : TraceStatus
    playerDeveloperAddress : Addresses developers player
    revealAddsProvenanceKnowledge : Bool
    revealInvalidatesAllPriorChoices : Bool
    fictionalityImpliesMeaninglessness : Bool
    revealReceipt : String

canonicalDeveloperMetaReveal : MetaReveal
canonicalDeveloperMetaReveal = record
  { beforeStatus = enactedFiction
  ; afterStatus = disclosedConstruction
  ; traceAfterReveal = causalTraceRetained
  ; playerDeveloperAddress = developersAddressPlayer
  ; revealAddsProvenanceKnowledge = true
  ; revealInvalidatesAllPriorChoices = false
  ; fictionalityImpliesMeaninglessness = false
  ; revealReceipt =
      "The final address discloses the construction relation while retaining the player's enacted history and its consequences within the run."
  }

------------------------------------------------------------------------
-- The review's theatre claim is stored as an interpretation, not a universal
-- theorem about every game.
------------------------------------------------------------------------

record PlayerDeveloperConversationCandidate : Set where
  field
    workLabel : String
    developerExpression : String
    playerEnactment : String
    theatreMakesRelationVisible : Bool
    allGamesUniversallyEquivalentClaimed : Bool
    interpretationCandidateOnly : Bool
    sourceReceipt : String

canonicalPathologicConversationCandidate :
  PlayerDeveloperConversationCandidate
canonicalPathologicConversationCandidate = record
  { workLabel = "Pathologic / Pathologic Classic HD"
  ; developerExpression = "rules, constraints, writing, theatrical framing and hidden provenance"
  ; playerEnactment = "route selection, survival decisions, cross-run memory and ending judgment"
  ; theatreMakesRelationVisible = true
  ; allGamesUniversallyEquivalentClaimed = false
  ; interpretationCandidateOnly = true
  ; sourceReceipt =
      "Formalises hbomberguy's reading that the final curtain exposes a conversation already enacted between player and developers."
  }

record PathologicTheatreAuthorityBoundary : Set where
  field
    playerCharacterDeveloperLayersTyped : Bool
    counterAgencyTyped : Bool
    metafictionErasesRunTrace : Bool
    childrenAreUltimateOntologyProved : Bool
    developerLayerIsUltimateMetaphysicsProved : Bool
    theatreReadingUniversalisedToAllGames : Bool
    boundaryNote : String

canonicalPathologicTheatreAuthorityBoundary :
  PathologicTheatreAuthorityBoundary
canonicalPathologicTheatreAuthorityBoundary = record
  { playerCharacterDeveloperLayersTyped = true
  ; counterAgencyTyped = true
  ; metafictionErasesRunTrace = false
  ; childrenAreUltimateOntologyProved = false
  ; developerLayerIsUltimateMetaphysicsProved = false
  ; theatreReadingUniversalisedToAllGames = false
  ; boundaryNote =
      "Metatheatre is represented as nested dependency and provenance. The reveal changes what the player knows about construction; it does not prove that prior experience was causally or aesthetically null."
  }
