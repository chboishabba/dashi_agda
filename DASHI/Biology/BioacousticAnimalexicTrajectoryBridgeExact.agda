module DASHI.Biology.BioacousticAnimalexicTrajectoryBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.AnimalexicFormalSystemExact as Animal
import DASHI.Biology.BioacousticStateSpaceVisualisationExact as Visual

------------------------------------------------------------------------
-- Cross-repository runtime ABI.
--
-- chboishabba/animalexic owns runtime governance and receipt production.
-- DASHI owns the formal observation / embedding / rendering boundaries.
-- This bridge records the least-privilege handoff between them.
------------------------------------------------------------------------

data RuntimeDecision : Set where
  candidate : RuntimeDecision
  promoted : RuntimeDecision
  abstain : RuntimeDecision
  reject : RuntimeDecision

record GovernedTrajectoryRow : Set where
  constructor governedTrajectoryRow
  field
    time : String
    x y z : String
    channel : String
    provenance : String
    decision : RuntimeDecision
    sourceIdentity : String
    residual : String
    receiptIdentity : String

open GovernedTrajectoryRow public

record AnimalexicTrajectoryABI : Set where
  constructor animalexicTrajectoryABI
  field
    schemaName : String
    requiredColumns : List String
    promotedOnlyDefault : Bool
    candidateRowsRemainInspectable : Bool
    abstainedRowsRemainInspectable : Bool
    rejectedRowsRemainInspectable : Bool
    canonicalMutationRequiresPromotion : Bool
    canonicalMutationRequiresReceipt : Bool
    provenanceRetainedPerRow : Bool

open AnimalexicTrajectoryABI public

canonicalAnimalexicTrajectoryABI : AnimalexicTrajectoryABI
canonicalAnimalexicTrajectoryABI =
  animalexicTrajectoryABI
    "animalexic-state-space-trajectory-v1"
    ("t" ∷ "x" ∷ "y" ∷ "z" ∷ "channel" ∷ "provenance" ∷
     "decision" ∷ "source_id" ∷ "residual" ∷ "receipt_id" ∷ [])
    true true true true true true true

------------------------------------------------------------------------
-- Source / producer coordinates discovered in the current web pass.
------------------------------------------------------------------------

record ExternalTrajectoryProducer : Set where
  constructor externalTrajectoryProducer
  field
    authorOrOwner : String
    title : String
    stableIdentifier : String
    producerClass : String
    relationshipToDASHI : String
    publicDataCarrier : String

open ExternalTrajectoryProducer public

areseSharedAcousticManifolds : ExternalTrajectoryProducer
areseSharedAcousticManifolds =
  externalTrajectoryProducer
    "Lucio Arese"
    "Shared acoustic manifolds for exploratory comparison of passerine vocalizations"
    "DOI:10.32942/X2W65N"
    "120D MFCC or 80D chroma -> PCA20 -> UMAP3 shared per-species manifolds; frame-aligned time trajectories"
    "real external bioacoustic trajectory producer; citation/data do not prove DASHI semantic claims"
    "Zenodo DOI:10.5281/zenodo.18332166; processed shared coordinates and frame-aligned descriptors"

soundPlotProducer : ExternalTrajectoryProducer
soundPlotProducer =
  externalTrajectoryProducer
    "Naqcho Ali Mehdi; Mohammad Adeel; Aizaz Ali Larik"
    "SoundPlot: An Open-Source Framework for Birdsong Acoustic Analysis and Neural Synthesis with Interactive 3D Visualization"
    "arXiv:2601.12752"
    "spectral/pYIN/MFCC feature extraction plus PCA and interactive Three.js trajectory"
    "open implementation/reference producer; not same-object with Arese or Animalexic"
    "open-source project described by the paper"

currentExternalTrajectoryProducers : List ExternalTrajectoryProducer
currentExternalTrajectoryProducers =
  areseSharedAcousticManifolds ∷ soundPlotProducer ∷ []

------------------------------------------------------------------------
-- Governance and interpretation firewalls.
------------------------------------------------------------------------

record GovernedTrajectoryBoundary : Set where
  constructor governedTrajectoryBoundary
  field
    candidateRowIsCanonicalState : Bool
    candidateRowIsCanonicalStateIsFalse : candidateRowIsCanonicalState ≡ false
    embeddingCoordinatesArePhysicalCoordinates : Bool
    embeddingCoordinatesArePhysicalCoordinatesIsFalse :
      embeddingCoordinatesArePhysicalCoordinates ≡ false
    visualRecurrenceImpliesSemanticMeaning : Bool
    visualRecurrenceImpliesSemanticMeaningIsFalse :
      visualRecurrenceImpliesSemanticMeaning ≡ false
    functionalTraceImpliesMaleCNSNeuronIdentity : Bool
    functionalTraceImpliesMaleCNSNeuronIdentityIsFalse :
      functionalTraceImpliesMaleCNSNeuronIdentity ≡ false
    externalCSVAutomaticallyPromoted : Bool
    externalCSVAutomaticallyPromotedIsFalse : externalCSVAutomaticallyPromoted ≡ false
    receiptAndPromotionRemainUpstreamObligations : Bool
    receiptAndPromotionRemainUpstreamObligationsIsTrue :
      receiptAndPromotionRemainUpstreamObligations ≡ true

open GovernedTrajectoryBoundary public

canonicalGovernedTrajectoryBoundary : GovernedTrajectoryBoundary
canonicalGovernedTrajectoryBoundary =
  governedTrajectoryBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl

------------------------------------------------------------------------
-- Reuse witness: the trajectory adapter is a consumer of Animalexic's
-- existing observation/promotion architecture, not a replacement for it.
------------------------------------------------------------------------

animalexicEpistemicBoundaryReused : Animal.AnimalexicEpistemicBoundary
animalexicEpistemicBoundaryReused = Animal.canonicalAnimalexicEpistemicBoundary

visualisationBoundaryReused : Visual.BioacousticVisualisationBoundary
visualisationBoundaryReused = Visual.canonicalBioacousticVisualisationBoundary

runtimeBridgeStatement : String
runtimeBridgeStatement =
  "Animalexic may export governed, provenance-bearing state-space rows for downstream rendering. Promotion status and receipt identity remain visible coordinates. Published external coordinates may be rendered as candidate diagnostics, but publication is not promotion. The renderer is a consumer over fibres through time, not an authority that can manufacture canonical geometry, semantic meaning, anatomical identity, or causal mechanism."
