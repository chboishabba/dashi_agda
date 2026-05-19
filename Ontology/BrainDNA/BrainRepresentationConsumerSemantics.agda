module Ontology.BrainDNA.BrainRepresentationConsumerSemantics where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
import Ontology.Brain.BrainRegionAutomatonSurface as Region
import Ontology.Brain.BrainVisualFormConstantSurface as Visual
import Ontology.BrainDNA.BrainDnaRepresentationMap as Map
import Ontology.BrainDNA.BrainRepresentationTransportLaws as Transport
import Ontology.BrainDNA.BrainRepresentationSemanticDepth as SemDepth
import Ontology.BrainDNA.BrainRepresentationSemanticLaws as SemLaw
import Ontology.BrainDNA.BrainConnectorEndToEndSemanticDepth as EndToEnd
import Ontology.BrainDNA.BrainChemistryCodecConsumer as Consumer
import Ontology.BrainDNA.BrainAtomicChemistryHandoff as Handoff
import Ontology.BrainDNA.PacketCodecBridge as Bridge
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)

------------------------------------------------------------------------
-- Bounded downstream consumer semantics over the current representation
-- chain.
--
-- This remains theorem-thin and non-claiming. It packages the current
-- representation map, transport laws, semantic-depth surface, and
-- semantic-law surface into one consumer-facing semantics object with exact
-- coherence over order/width/admissibility/recovery/theme alignment.

record BrainRepresentationConsumerProfile (n : Nat) : Set₁ where
  constructor mkBrainRepresentationConsumerProfile
  field
    representationSemantics : Map.BrainDnaRepresentationSemantics n
    transportProfile : Transport.BrainRepresentationTransportProfile n
    semanticDepth : SemDepth.BrainRepresentationSemanticDepthProfile n
    semanticLaw : SemLaw.BrainRepresentationSemanticLawProfile n
    endToEnd : EndToEnd.BrainConnectorEndToEndSemanticProfile n
    order : ScanOrder
    width : Nat
    encodedAdmissibility : Bool
    emittedAdmissibility : Bool
    recoveryBoundary : Nat
    visualClass : Visual.BrainVisualFormConstant

brainRepresentationConsumerProfile :
  ∀ {n} → BrainState n → Region.BrainRegion → BrainRepresentationConsumerProfile n
brainRepresentationConsumerProfile st r =
  mkBrainRepresentationConsumerProfile
    (Map.representationSemanticsOf st r)
    (Transport.representationTransportProfileOf st r)
    (SemDepth.brainRepresentationSemanticDepthProfile st r)
    (SemLaw.brainRepresentationSemanticLawProfile st r)
    (EndToEnd.brainConnectorEndToEndSemanticProfile st r)
    (SemLaw.BrainRepresentationSemanticLawProfile.order
      (SemLaw.brainRepresentationSemanticLawProfile st r))
    (SemLaw.BrainRepresentationSemanticLawProfile.width
      (SemLaw.brainRepresentationSemanticLawProfile st r))
    (SemLaw.BrainRepresentationSemanticLawProfile.encodedAdmissibility
      (SemLaw.brainRepresentationSemanticLawProfile st r))
    (SemLaw.BrainRepresentationSemanticLawProfile.emittedAdmissibility
      (SemLaw.brainRepresentationSemanticLawProfile st r))
    (SemLaw.BrainRepresentationSemanticLawProfile.recoveryBoundary
      (SemLaw.brainRepresentationSemanticLawProfile st r))
    (SemLaw.BrainRepresentationSemanticLawProfile.visualClass
      (SemLaw.brainRepresentationSemanticLawProfile st r))

consumerOrderMatchesSemanticLaw :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerProfile.order
    (brainRepresentationConsumerProfile st r)
    ≡
  SemLaw.BrainRepresentationSemanticLawProfile.order
    (SemLaw.brainRepresentationSemanticLawProfile st r)
consumerOrderMatchesSemanticLaw st r = refl

consumerOrderMatchesEndToEnd :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerProfile.order
    (brainRepresentationConsumerProfile st r)
    ≡
  EndToEnd.BrainConnectorEndToEndSemanticProfile.order
    (EndToEnd.brainConnectorEndToEndSemanticProfile st r)
consumerOrderMatchesEndToEnd st r = refl

consumerOrderLineMajor :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerProfile.order
    (brainRepresentationConsumerProfile st r)
    ≡
  lineMajor
consumerOrderLineMajor st r =
  SemLaw.semanticLawOrderLineMajor st r

consumerWidthMatchesSemanticLaw :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerProfile.width
    (brainRepresentationConsumerProfile st r)
    ≡
  SemLaw.BrainRepresentationSemanticLawProfile.width
    (SemLaw.brainRepresentationSemanticLawProfile st r)
consumerWidthMatchesSemanticLaw st r = refl

consumerWidthMatchesEndToEnd :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerProfile.width
    (brainRepresentationConsumerProfile st r)
    ≡
  EndToEnd.BrainConnectorEndToEndSemanticProfile.width
    (EndToEnd.brainConnectorEndToEndSemanticProfile st r)
consumerWidthMatchesEndToEnd st r = refl

consumerWidthExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerProfile.width
    (brainRepresentationConsumerProfile st r)
    ≡
  n
consumerWidthExact st r =
  SemLaw.semanticLawWidthExact st r

consumerEncodedAdmissibilityMatchesSemanticLaw :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerProfile.encodedAdmissibility
    (brainRepresentationConsumerProfile st r)
    ≡
  SemLaw.BrainRepresentationSemanticLawProfile.encodedAdmissibility
    (SemLaw.brainRepresentationSemanticLawProfile st r)
consumerEncodedAdmissibilityMatchesSemanticLaw st r = refl

consumerEncodedAdmissibilityMatchesRepresentation :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerProfile.encodedAdmissibility
    (brainRepresentationConsumerProfile st r)
    ≡
  Bridge.packetAdmissibility
    (Map.BrainDnaRepresentation.packet
      (Map.BrainDnaRepresentationSemantics.representation
        (Map.representationSemanticsOf st r)))
consumerEncodedAdmissibilityMatchesRepresentation st r =
  SemLaw.semanticLawEncodedAdmissibilityMatchesRepresentation st r

consumerEmittedAdmissibilityMatchesSemanticLaw :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerProfile.emittedAdmissibility
    (brainRepresentationConsumerProfile st r)
    ≡
  SemLaw.BrainRepresentationSemanticLawProfile.emittedAdmissibility
    (SemLaw.brainRepresentationSemanticLawProfile st r)
consumerEmittedAdmissibilityMatchesSemanticLaw st r = refl

consumerEmittedAdmissibilityMatchesEndToEnd :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerProfile.emittedAdmissibility
    (brainRepresentationConsumerProfile st r)
    ≡
  EndToEnd.BrainConnectorEndToEndSemanticProfile.emittedAdmissibility
    (EndToEnd.brainConnectorEndToEndSemanticProfile st r)
consumerEmittedAdmissibilityMatchesEndToEnd st r = refl

consumerEmittedAdmissibilityMatchesChemistryConsumer :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerProfile.emittedAdmissibility
    (brainRepresentationConsumerProfile st r)
    ≡
  Consumer.BrainChemistryCodecConsumerProfile.emittedAdmissibility
    (Consumer.brainChemistryCodecConsumerProfile st)
consumerEmittedAdmissibilityMatchesChemistryConsumer st r =
  SemLaw.semanticLawEmittedAdmissibilityMatchesConsumer st r

consumerRecoveryMatchesSemanticLaw :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerProfile.recoveryBoundary
    (brainRepresentationConsumerProfile st r)
    ≡
  SemLaw.BrainRepresentationSemanticLawProfile.recoveryBoundary
    (SemLaw.brainRepresentationSemanticLawProfile st r)
consumerRecoveryMatchesSemanticLaw st r = refl

consumerRecoveryMatchesEndToEnd :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerProfile.recoveryBoundary
    (brainRepresentationConsumerProfile st r)
    ≡
  EndToEnd.BrainConnectorEndToEndSemanticProfile.recoveryBoundary
    (EndToEnd.brainConnectorEndToEndSemanticProfile st r)
consumerRecoveryMatchesEndToEnd st r = refl

consumerRecoveryExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerProfile.recoveryBoundary
    (brainRepresentationConsumerProfile st r)
    ≡
  3
consumerRecoveryExact st r =
  SemLaw.semanticLawRecoveryExact st r

consumerRecoveryMatchesHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerProfile.recoveryBoundary
    (brainRepresentationConsumerProfile st r)
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.recoveryBoundary
    (Handoff.brainAtomicChemistryHandoffProfileOf st)
consumerRecoveryMatchesHandoff st r =
  SemLaw.semanticLawRecoveryMatchesHandoff st r

consumerVisualClassMatchesSemanticLaw :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerProfile.visualClass
    (brainRepresentationConsumerProfile st r)
    ≡
  SemLaw.BrainRepresentationSemanticLawProfile.visualClass
    (SemLaw.brainRepresentationSemanticLawProfile st r)
consumerVisualClassMatchesSemanticLaw st r = refl

record BrainRepresentationConsumerSemanticSurface : Setω where
  field
    representationMap : Map.BrainDnaRepresentationMapSurface
    transportLaws : Transport.BrainRepresentationTransportLawSurface
    semanticDepth : SemDepth.BrainRepresentationSemanticDepthSurface
    semanticLaws : SemLaw.BrainRepresentationSemanticLawSurface
    consumerProfile :
      ∀ {n} → BrainState n → Region.BrainRegion → BrainRepresentationConsumerProfile n

brainRepresentationConsumerSemanticSurface : BrainRepresentationConsumerSemanticSurface
brainRepresentationConsumerSemanticSurface = record
  { representationMap = Map.brainDnaRepresentationMapSurface
  ; transportLaws = Transport.brainRepresentationTransportLawSurface
  ; semanticDepth = SemDepth.brainRepresentationSemanticDepthSurface
  ; semanticLaws = SemLaw.brainRepresentationSemanticLawSurface
  ; consumerProfile = brainRepresentationConsumerProfile
  }
