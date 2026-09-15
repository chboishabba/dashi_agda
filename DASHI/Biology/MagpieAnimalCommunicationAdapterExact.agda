module DASHI.Biology.MagpieAnimalCommunicationAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.MagpieVocalAtlasObservationExact as MagpieObservation
import DASHI.Biology.MagpieVocalAtlasLatentExact as MagpieLatent
import DASHI.Biology.MagpieSemanticPromotionExact as MagpieSemantic
import DASHI.Biology.AnimalCommunicationSceneObservationExact as Scene
import DASHI.Biology.AnimalCommunicationLatentExact as GenericLatent
import DASHI.Biology.AnimalCommunicationSemanticEvidenceExact as GenericSemantic

------------------------------------------------------------------------
-- APPEND-ONLY ADAPTER FROM THE MERGED MAGPIE ATLAS INTO THE GENERIC CORE.
-- It preserves references and unpaid coordinates; it does not reinterpret old
-- receipts as stronger generic communication/semantic evidence.
------------------------------------------------------------------------

magpieEventToGenericScene :
  MagpieObservation.MagpieVocalEvent → Scene.AnimalCommunicationScene
magpieEventToGenericScene event =
  Scene.animal-communication-scene
    (MagpieObservation.eventId event)
    (MagpieObservation.sourceId event)
    (MagpieObservation.sourceClockReference event)
    (MagpieObservation.physicalTimeContext event)
    (MagpieObservation.habitatEnvironmentContext event)
    (MagpieObservation.observedSurrounds event)
    ((MagpieObservation.sourceId event) ∷ [])
    []
    ((MagpieObservation.eventId event) ∷ [])
    (MagpieObservation.receiptReferences event)

magpieLatentFibreToGeneric :
  MagpieLatent.MagpieLatentFibre → GenericLatent.CommunicationLatentFibre
magpieLatentFibreToGeneric MagpieLatent.acousticForm = GenericLatent.signalFormFibre
magpieLatentFibreToGeneric MagpieLatent.semanticCore = GenericLatent.functionalSemanticHypothesisFibre
magpieLatentFibreToGeneric MagpieLatent.geographicRealisation = GenericLatent.groupPopulationGeographicFibre
magpieLatentFibreToGeneric MagpieLatent.groupSyntax = GenericLatent.interactionTurnFibre
magpieLatentFibreToGeneric MagpieLatent.individualVoice = GenericLatent.individualRealisationFibre
magpieLatentFibreToGeneric MagpieLatent.situatedContext = GenericLatent.historyContextFibre
magpieLatentFibreToGeneric MagpieLatent.environment = GenericLatent.environmentFibre
magpieLatentFibreToGeneric MagpieLatent.recordingProvenance = GenericLatent.recordingProvenanceFibre

record MagpieGenericAdapterReceipt : Set where
  constructor magpie-generic-adapter-receipt
  field
    magpieEventReference : String
    genericSceneReference : String
    originalObservationOwner : String
    originalLatentOwner : String
    originalSemanticOwner : String
    genericSceneOwner : String
    genericLatentOwner : String
    genericSemanticOwner : String
    receiverIdentityPayment : GenericSemantic.PaymentStatus
    interactionPayment : GenericSemantic.PaymentStatus
    semanticPayment : GenericSemantic.PaymentStatus
    preservesOriginalReceipts : Bool

open MagpieGenericAdapterReceipt public

magpieSeedAdapterReceipt : MagpieGenericAdapterReceipt
magpieSeedAdapterReceipt = magpie-generic-adapter-receipt
  "MagpieVocalAtlasObservationExact.initialAtlasObservations"
  "derived generic scene references only"
  "DASHI.Biology.MagpieVocalAtlasObservationExact"
  "DASHI.Biology.MagpieVocalAtlasLatentExact"
  "DASHI.Biology.MagpieSemanticPromotionExact"
  "DASHI.Biology.AnimalCommunicationSceneObservationExact"
  "DASHI.Biology.AnimalCommunicationLatentExact"
  "DASHI.Biology.AnimalCommunicationSemanticEvidenceExact"
  GenericSemantic.unpaid
  GenericSemantic.unpaid
  GenericSemantic.unpaid
  true

record MagpieAdapterBoundary : Set where
  constructor magpie-adapter-boundary
  field
    magpieAdapterDoesNotPromoteSemantics : Bool
    adapterAddsReceiverIdentity : Bool
    adapterAddsInteractionAuthority : Bool
    adapterAddsCrossSpeciesMeaning : Bool
    adapterRewritesHistoricalMagpieReceipts : Bool
    adapterPreservesUnresolvedCoordinates : Bool
    adapterRetainsSourceProvenance : Bool

open MagpieAdapterBoundary public

canonicalMagpieAdapterBoundary : MagpieAdapterBoundary
canonicalMagpieAdapterBoundary =
  magpie-adapter-boundary true false false false false true true

adapterReading : String
adapterReading =
  "The generic AnimalCommunication core sits beneath the existing magpie atlas by reference-preserving adaptation. Existing magpie source/time/environment and latent-fibre distinctions are exposed to generic consumers, while receiver identity, interaction authority and semantic payments remain unpaid unless separately observed."
