module DASHI.Biology.RuinNarrativeReorganisationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.TypedHyperfabricCore as Hyperfabric

------------------------------------------------------------------------
-- Ruins retain several temporal organisations on one material carrier.
-- Reoccupation changes incidence and transport without erasing provenance.
------------------------------------------------------------------------

data RuinUse : Set where
  abandonedUse : RuinUse
  commercialUse : RuinUse
  shelterUse : RuinUse
  researchUse : RuinUse
  danceUse : RuinUse
  commonsUse : RuinUse
  erasedUse : RuinUse

data Affordance : Set where
  pastCommerce : Affordance
  presentShelter : Affordance
  investigation : Affordance
  collectiveDance : Affordance
  futureCommons : Affordance

record RuinState : Set where
  constructor ruinState
  field
    materialCarrier : String
    historicalUse : RuinUse
    presentUse : RuinUse
    latentUses : List RuinUse
    provenance : List String

open RuinState public

abandonedRuin : RuinState
abandonedRuin =
  ruinState "church-commercial shell" commercialUse abandonedUse
    (researchUse ∷ danceUse ∷ shelterUse ∷ [])
    ("religious history" ∷ "commercial failure" ∷ "present occupation" ∷ [])

reoccupiedRuin : RuinState
reoccupiedRuin =
  ruinState "church-commercial shell" commercialUse danceUse
    (researchUse ∷ shelterUse ∷ commonsUse ∷ [])
    ("religious history" ∷ "commercial failure" ∷ "present occupation" ∷ [])

reoccupationRetainsMaterialCarrier :
  materialCarrier abandonedRuin ≡ materialCarrier reoccupiedRuin
reoccupationRetainsMaterialCarrier = refl

reoccupationRetainsProvenance :
  provenance abandonedRuin ≡ provenance reoccupiedRuin
reoccupationRetainsProvenance = refl

reoccupationChangesPresentUse :
  ¬ (presentUse abandonedRuin ≡ presentUse reoccupiedRuin)
reoccupationChangesPresentUse ()

reoccupationIsNotErasure :
  ¬ (presentUse reoccupiedRuin ≡ erasedUse)
reoccupationIsNotErasure ()

------------------------------------------------------------------------
-- Narrative-affordance feedback: a shared doom narrative can alter action,
-- occupation and later evidence without becoming a supernatural fact.
------------------------------------------------------------------------

data FeedbackStage : Set where
  doomNarrativeStage : FeedbackStage
  constrainedActionStage : FeedbackStage
  failedOccupationStage : FeedbackStage
  reinforcedNarrativeStage : FeedbackStage

nextFeedbackStage : FeedbackStage → FeedbackStage
nextFeedbackStage doomNarrativeStage = constrainedActionStage
nextFeedbackStage constrainedActionStage = failedOccupationStage
nextFeedbackStage failedOccupationStage = reinforcedNarrativeStage
nextFeedbackStage reinforcedNarrativeStage = doomNarrativeStage

feedbackLoopClosesInFourSteps :
  nextFeedbackStage
    (nextFeedbackStage
      (nextFeedbackStage
        (nextFeedbackStage doomNarrativeStage)))
  ≡ doomNarrativeStage
feedbackLoopClosesInFourSteps = refl

------------------------------------------------------------------------
-- Concrete TypedHyperfabric reorganisation: before reoccupation there is no
-- participant-to-site incidence; afterwards there is one.  Stalk carrier and
-- edge provenance remain unchanged.
------------------------------------------------------------------------

data RuinVertex : Set where
  participantVertex : RuinVertex

data RuinEdge : Set where
  ruinAssemblyEdge : RuinEdge

beforeRuinFabric : Hyperfabric.TypedHyperfabric RuinVertex RuinEdge
beforeRuinFabric = record
  { Hyperfabric.vertexStalk = λ vertex → ⊤
  ; Hyperfabric.edgeStalk = λ edge → ⊤
  ; Hyperfabric.incidence = λ vertex edge → ⊥
  ; Hyperfabric.restrict = λ membership value → ⊥-elim membership
  ; Hyperfabric.edgeProvenance = λ edge →
      "church-commercial shell provenance" ∷ []
  ; Hyperfabric.edgeSalience = λ edge → 6
  ; Hyperfabric.fabricLabel = "ruin before reoccupation"
  }

afterRuinFabric : Hyperfabric.TypedHyperfabric RuinVertex RuinEdge
afterRuinFabric = record
  { Hyperfabric.vertexStalk = λ vertex → ⊤
  ; Hyperfabric.edgeStalk = λ edge → ⊤
  ; Hyperfabric.incidence = λ vertex edge → ⊤
  ; Hyperfabric.restrict = λ membership value → tt
  ; Hyperfabric.edgeProvenance = λ edge →
      "church-commercial shell provenance" ∷ []
  ; Hyperfabric.edgeSalience = λ edge → 6
  ; Hyperfabric.fabricLabel = "ruin after reoccupation"
  }

reoccupiedGlobalSection : Hyperfabric.GlobalSection afterRuinFabric
reoccupiedGlobalSection = record
  { Hyperfabric.vertexValue = λ vertex → tt
  ; Hyperfabric.edgeValue = λ edge → tt
  ; Hyperfabric.compatible = λ membership → refl
  ; Hyperfabric.sectionReceipt = "new participant/site incidence is compatible"
  }

ruinReorganisation :
  Hyperfabric.ProvenancePreservingReorganisation
    beforeRuinFabric afterRuinFabric
ruinReorganisation = record
  { Hyperfabric.edgeMap = λ edge → edge
  ; Hyperfabric.provenancePreserved = λ edge → refl
  ; Hyperfabric.incidenceMayChange = true
  ; Hyperfabric.transportMayChange = true
  ; Hyperfabric.stalkContentErased = false
  ; Hyperfabric.reorganisationReceipt =
      "reoccupation changes relational access without erasing the carrier"
  }

ruinReorganisationDeclaresNoStalkErasure :
  Hyperfabric.stalkContentErased ruinReorganisation ≡ false
ruinReorganisationDeclaresNoStalkErasure = refl

record RuinReorganisationBoundary : Set where
  constructor ruinReorganisationBoundary
  field
    ruinIsDeadRemainderOnly : Bool
    ruinIsDeadRemainderOnlyIsFalse : ruinIsDeadRemainderOnly ≡ false
    reoccupationEqualsRestoration : Bool
    reoccupationEqualsRestorationIsFalse :
      reoccupationEqualsRestoration ≡ false
    doomNarrativeIsSupernaturalCausationProved : Bool
    doomNarrativeIsSupernaturalCausationProvedIsFalse :
      doomNarrativeIsSupernaturalCausationProved ≡ false
    changedIncidenceRequiresProvenanceErasure : Bool
    changedIncidenceRequiresProvenanceErasureIsFalse :
      changedIncidenceRequiresProvenanceErasure ≡ false

canonicalRuinReorganisationBoundary : RuinReorganisationBoundary
canonicalRuinReorganisationBoundary =
  ruinReorganisationBoundary false refl false refl false refl false refl
