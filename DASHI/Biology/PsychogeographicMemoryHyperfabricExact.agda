module DASHI.Biology.PsychogeographicMemoryHyperfabricExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Biology.AssociativeDivinationPNFExact as Association
import DASHI.Reasoning.TypedHyperfabricCore as Hyperfabric

------------------------------------------------------------------------
-- This module reuses the repository's exact MemoryFibre preservation
-- theorems and TypedHyperfabric carrier.  The city is represented as a
-- relational field of bodies, sites, people, institutions, histories,
-- symbols and ecologies rather than as a graph of streets alone.
------------------------------------------------------------------------

data PsychVertex : Set where
  bodyVertex : PsychVertex
  siteVertex : PsychVertex
  personVertex : PsychVertex
  institutionVertex : PsychVertex
  eventVertex : PsychVertex
  symbolVertex : PsychVertex
  ecologyVertex : PsychVertex

data PsychEdge : Set where
  livedSituationEdge : PsychEdge
  collectiveHistoryEdge : PsychEdge
  placeMemoryEdge : PsychEdge

record PlaceMemoryState : Set where
  constructor placeMemoryState
  field
    memory : Memory.MemoryFibre
    affectiveIntensity : Nat
    actionReadiness : Nat
    activeRetrieval : Association.RetrievalFibre
    placeLabel : String
    relationLabel : String

open PlaceMemoryState public

revaluePlace : PlaceMemoryState → Nat → PlaceMemoryState
revaluePlace state value =
  placeMemoryState
    (Memory.revalue (memory state) value)
    (affectiveIntensity state)
    (actionReadiness state)
    (activeRetrieval state)
    (placeLabel state)
    (relationLabel state)

habituatePlace : PlaceMemoryState → PlaceMemoryState
habituatePlace state =
  placeMemoryState
    (Memory.habituate (memory state))
    (affectiveIntensity state)
    (actionReadiness state)
    (activeRetrieval state)
    (placeLabel state)
    (relationLabel state)

extinguishPlaceActionDominance : PlaceMemoryState → PlaceMemoryState
extinguishPlaceActionDominance state =
  placeMemoryState
    (Memory.extinguishActionDominance (memory state))
    (affectiveIntensity state)
    0
    (activeRetrieval state)
    (placeLabel state)
    "association retained; compulsory action inhibited"

realignPlacePhase : PlaceMemoryState → Nat → PlaceMemoryState
realignPlacePhase state newPhase =
  placeMemoryState
    (Memory.realignPhase (memory state) newPhase)
    (affectiveIntensity state)
    (actionReadiness state)
    (activeRetrieval state)
    (placeLabel state)
    (relationLabel state)

placeRevaluationPreservesRememberedEvent :
  ∀ state value →
  Memory.rememberedEvent (memory (revaluePlace state value))
  ≡ Memory.rememberedEvent (memory state)
placeRevaluationPreservesRememberedEvent state value =
  Memory.revaluePreservesRememberedEvent (memory state) value

placeHabituationPreservesRememberedEvent :
  ∀ state →
  Memory.rememberedEvent (memory (habituatePlace state))
  ≡ Memory.rememberedEvent (memory state)
placeHabituationPreservesRememberedEvent state =
  Memory.habituationPreservesRememberedEvent (memory state)

placeExtinctionPreservesRememberedEvent :
  ∀ state →
  Memory.rememberedEvent (memory (extinguishPlaceActionDominance state))
  ≡ Memory.rememberedEvent (memory state)
placeExtinctionPreservesRememberedEvent state =
  Memory.extinctionPreservesRememberedEvent (memory state)

placePhaseRealignmentPreservesRememberedEvent :
  ∀ state newPhase →
  Memory.rememberedEvent (memory (realignPlacePhase state newPhase))
  ≡ Memory.rememberedEvent (memory state)
placePhaseRealignmentPreservesRememberedEvent state newPhase = refl

------------------------------------------------------------------------
-- The generic psychogeographic hyperfabric leaves the concrete stalk model
-- parameterised but fixes higher-arity urban incidence and provenance.
------------------------------------------------------------------------

PsychStalk : Set → PsychVertex → Set
PsychStalk State vertex = State

PsychEdgeStalk : Set → PsychEdge → Set
PsychEdgeStalk State edge = State

psychogeographicHyperfabric :
  (State : Set) →
  Hyperfabric.TypedHyperfabric PsychVertex PsychEdge
psychogeographicHyperfabric State = record
  { Hyperfabric.vertexStalk = PsychStalk State
  ; Hyperfabric.edgeStalk = PsychEdgeStalk State
  ; Hyperfabric.incidence = λ vertex edge → ⊤
  ; Hyperfabric.restrict = λ membership state → state
  ; Hyperfabric.edgeProvenance = edgeProvenanceFor
  ; Hyperfabric.edgeSalience = edgeSalienceFor
  ; Hyperfabric.fabricLabel = "path-indexed psychogeographic memory hyperfabric"
  }
  where
  edgeProvenanceFor : PsychEdge → List String
  edgeProvenanceFor livedSituationEdge =
    "body/place/time/relation/event" ∷ []
  edgeProvenanceFor collectiveHistoryEdge =
    "institution/public narrative/suppressed narrative" ∷ []
  edgeProvenanceFor placeMemoryEdge =
    "place cue/memory fibre/retrieval channel" ∷ []

  edgeSalienceFor : PsychEdge → Nat
  edgeSalienceFor livedSituationEdge = 3
  edgeSalienceFor collectiveHistoryEdge = 5
  edgeSalienceFor placeMemoryEdge = 7

canonicalPsychogeographicTrace : Hyperfabric.HyperfabricTrace PsychEdge
canonicalPsychogeographicTrace = record
  { Hyperfabric.visitedEdges =
      livedSituationEdge ∷ placeMemoryEdge ∷ collectiveHistoryEdge ∷ []
  ; Hyperfabric.traceReceipts =
      "embodied encounter" ∷ "retrieval" ∷ "historical reframing" ∷ []
  ; Hyperfabric.traceLabel = "psychogeographic derive trace"
  }

canonicalRetrievalChannelsAreReused : List Association.RetrievalFibre
canonicalRetrievalChannelsAreReused = Association.canonicalNarrativeRetrievalFibres

record PsychogeographicMemoryBoundary : Set where
  constructor psychogeographicMemoryBoundary
  field
    revaluationErasesEvent : Bool
    revaluationErasesEventIsFalse : revaluationErasesEvent ≡ false
    inhibitoryExtinctionErasesAssociation : Bool
    inhibitoryExtinctionErasesAssociationIsFalse :
      inhibitoryExtinctionErasesAssociation ≡ false
    everyLearningModeAutomaticallyPreservesEvent : Bool
    everyLearningModeAutomaticallyPreservesEventIsFalse :
      everyLearningModeAutomaticallyPreservesEvent ≡ false
    oneMemoryScalarDeterminesWholePlace : Bool
    oneMemoryScalarDeterminesWholePlaceIsFalse :
      oneMemoryScalarDeterminesWholePlace ≡ false

canonicalPsychogeographicMemoryBoundary : PsychogeographicMemoryBoundary
canonicalPsychogeographicMemoryBoundary =
  psychogeographicMemoryBoundary false refl false refl false refl false refl
