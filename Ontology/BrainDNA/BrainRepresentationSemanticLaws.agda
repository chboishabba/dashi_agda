module Ontology.BrainDNA.BrainRepresentationSemanticLaws where

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
import Ontology.BrainDNA.BrainConnectorEndToEndSemanticDepth as EndToEnd
import Ontology.BrainDNA.BrainChemistryCodecConsumer as Consumer
import Ontology.BrainDNA.BrainAtomicChemistryHandoff as Handoff
import Ontology.BrainDNA.PacketCodecBridge as Bridge
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)

------------------------------------------------------------------------
-- Bounded semantic/law surface over the current end-to-end representation
-- chain.
--
-- This remains theorem-thin and non-claiming. It packages exact/coherence
-- witnesses over the already-landed representation, transport,
-- semantic-depth, and end-to-end semantic-depth surfaces.

record BrainRepresentationSemanticLawProfile (n : Nat) : Set₁ where
  constructor mkBrainRepresentationSemanticLawProfile
  field
    representationSemantics : Map.BrainDnaRepresentationSemantics n
    semanticDepth : SemDepth.BrainRepresentationSemanticDepthProfile n
    endToEnd : EndToEnd.BrainConnectorEndToEndSemanticProfile n
    order : ScanOrder
    width : Nat
    encodedAdmissibility : Bool
    emittedAdmissibility : Bool
    recoveryBoundary : Nat
    visualClass : Visual.BrainVisualFormConstant

brainRepresentationSemanticLawProfile :
  ∀ {n} → BrainState n → Region.BrainRegion → BrainRepresentationSemanticLawProfile n
brainRepresentationSemanticLawProfile st r =
  mkBrainRepresentationSemanticLawProfile
    (Map.representationSemanticsOf st r)
    (SemDepth.brainRepresentationSemanticDepthProfile st r)
    (EndToEnd.brainConnectorEndToEndSemanticProfile st r)
    (SemDepth.BrainRepresentationSemanticDepthProfile.order
      (SemDepth.brainRepresentationSemanticDepthProfile st r))
    (SemDepth.BrainRepresentationSemanticDepthProfile.width
      (SemDepth.brainRepresentationSemanticDepthProfile st r))
    (SemDepth.BrainRepresentationSemanticDepthProfile.encodedAdmissibility
      (SemDepth.brainRepresentationSemanticDepthProfile st r))
    (SemDepth.BrainRepresentationSemanticDepthProfile.emittedAdmissibility
      (SemDepth.brainRepresentationSemanticDepthProfile st r))
    (SemDepth.BrainRepresentationSemanticDepthProfile.recoveryBoundary
      (SemDepth.brainRepresentationSemanticDepthProfile st r))
    (SemDepth.BrainRepresentationSemanticDepthProfile.visualClass
      (SemDepth.brainRepresentationSemanticDepthProfile st r))

semanticLawOrderMatchesSemanticDepth :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationSemanticLawProfile.order
    (brainRepresentationSemanticLawProfile st r)
    ≡
  SemDepth.BrainRepresentationSemanticDepthProfile.order
    (SemDepth.brainRepresentationSemanticDepthProfile st r)
semanticLawOrderMatchesSemanticDepth st r = refl

semanticLawOrderMatchesEndToEnd :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationSemanticLawProfile.order
    (brainRepresentationSemanticLawProfile st r)
    ≡
  EndToEnd.BrainConnectorEndToEndSemanticProfile.order
    (EndToEnd.brainConnectorEndToEndSemanticProfile st r)
semanticLawOrderMatchesEndToEnd st r = refl

semanticLawOrderLineMajor :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationSemanticLawProfile.order
    (brainRepresentationSemanticLawProfile st r)
    ≡
  lineMajor
semanticLawOrderLineMajor st r =
  SemDepth.representationSemanticDepthOrderLineMajor st r

semanticLawWidthMatchesSemanticDepth :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationSemanticLawProfile.width
    (brainRepresentationSemanticLawProfile st r)
    ≡
  SemDepth.BrainRepresentationSemanticDepthProfile.width
    (SemDepth.brainRepresentationSemanticDepthProfile st r)
semanticLawWidthMatchesSemanticDepth st r = refl

semanticLawWidthMatchesEndToEnd :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationSemanticLawProfile.width
    (brainRepresentationSemanticLawProfile st r)
    ≡
  EndToEnd.BrainConnectorEndToEndSemanticProfile.width
    (EndToEnd.brainConnectorEndToEndSemanticProfile st r)
semanticLawWidthMatchesEndToEnd st r = refl

semanticLawWidthExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationSemanticLawProfile.width
    (brainRepresentationSemanticLawProfile st r)
    ≡
  n
semanticLawWidthExact st r =
  SemDepth.representationSemanticDepthWidthExact st r

semanticLawEncodedAdmissibilityMatchesRepresentation :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationSemanticLawProfile.encodedAdmissibility
    (brainRepresentationSemanticLawProfile st r)
    ≡
  Bridge.packetAdmissibility
    (Map.BrainDnaRepresentation.packet
      (Map.BrainDnaRepresentationSemantics.representation
        (Map.representationSemanticsOf st r)))
semanticLawEncodedAdmissibilityMatchesRepresentation st r =
  SemDepth.representationSemanticDepthEncodedAdmissibilityMatchesPacket st r

semanticLawEmittedAdmissibilityMatchesSemanticDepth :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationSemanticLawProfile.emittedAdmissibility
    (brainRepresentationSemanticLawProfile st r)
    ≡
  SemDepth.BrainRepresentationSemanticDepthProfile.emittedAdmissibility
    (SemDepth.brainRepresentationSemanticDepthProfile st r)
semanticLawEmittedAdmissibilityMatchesSemanticDepth st r = refl

semanticLawEmittedAdmissibilityMatchesEndToEnd :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationSemanticLawProfile.emittedAdmissibility
    (brainRepresentationSemanticLawProfile st r)
    ≡
  EndToEnd.BrainConnectorEndToEndSemanticProfile.emittedAdmissibility
    (EndToEnd.brainConnectorEndToEndSemanticProfile st r)
semanticLawEmittedAdmissibilityMatchesEndToEnd st r = refl

semanticLawEmittedAdmissibilityMatchesConsumer :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationSemanticLawProfile.emittedAdmissibility
    (brainRepresentationSemanticLawProfile st r)
    ≡
  Consumer.BrainChemistryCodecConsumerProfile.emittedAdmissibility
    (Consumer.brainChemistryCodecConsumerProfile st)
semanticLawEmittedAdmissibilityMatchesConsumer st r =
  EndToEnd.endToEndAdmissibilityMatchesConsumer st r

semanticLawRecoveryMatchesSemanticDepth :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationSemanticLawProfile.recoveryBoundary
    (brainRepresentationSemanticLawProfile st r)
    ≡
  SemDepth.BrainRepresentationSemanticDepthProfile.recoveryBoundary
    (SemDepth.brainRepresentationSemanticDepthProfile st r)
semanticLawRecoveryMatchesSemanticDepth st r = refl

semanticLawRecoveryMatchesEndToEnd :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationSemanticLawProfile.recoveryBoundary
    (brainRepresentationSemanticLawProfile st r)
    ≡
  EndToEnd.BrainConnectorEndToEndSemanticProfile.recoveryBoundary
    (EndToEnd.brainConnectorEndToEndSemanticProfile st r)
semanticLawRecoveryMatchesEndToEnd st r = refl

semanticLawRecoveryExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationSemanticLawProfile.recoveryBoundary
    (brainRepresentationSemanticLawProfile st r)
    ≡
  3
semanticLawRecoveryExact st r =
  SemDepth.representationSemanticDepthRecoveryExact st r

semanticLawRecoveryMatchesHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationSemanticLawProfile.recoveryBoundary
    (brainRepresentationSemanticLawProfile st r)
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.recoveryBoundary
    (Handoff.brainAtomicChemistryHandoffProfileOf st)
semanticLawRecoveryMatchesHandoff st r =
  SemDepth.representationSemanticDepthRecoveryMatchesHandoff st r

semanticLawVisualClassMatchesSemanticDepth :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationSemanticLawProfile.visualClass
    (brainRepresentationSemanticLawProfile st r)
    ≡
  SemDepth.BrainRepresentationSemanticDepthProfile.visualClass
    (SemDepth.brainRepresentationSemanticDepthProfile st r)
semanticLawVisualClassMatchesSemanticDepth st r = refl

record BrainRepresentationSemanticLawSurface : Setω where
  field
    representationMap : Map.BrainDnaRepresentationMapSurface
    transportLaws : Transport.BrainRepresentationTransportLawSurface
    semanticDepth : SemDepth.BrainRepresentationSemanticDepthSurface
    endToEndSemanticDepth : EndToEnd.BrainConnectorEndToEndSemanticDepthSurface
    semanticLawProfile :
      ∀ {n} → BrainState n → Region.BrainRegion → BrainRepresentationSemanticLawProfile n

brainRepresentationSemanticLawSurface : BrainRepresentationSemanticLawSurface
brainRepresentationSemanticLawSurface = record
  { representationMap = Map.brainDnaRepresentationMapSurface
  ; transportLaws = Transport.brainRepresentationTransportLawSurface
  ; semanticDepth = SemDepth.brainRepresentationSemanticDepthSurface
  ; endToEndSemanticDepth = EndToEnd.brainConnectorEndToEndSemanticDepthSurface
  ; semanticLawProfile = brainRepresentationSemanticLawProfile
  }
