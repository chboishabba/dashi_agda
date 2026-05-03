module Ontology.BrainDNA.BrainRepresentationConsumerLaws where

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
import Ontology.BrainDNA.BrainRepresentationConsumerSemantics as ConsumerSem
import Ontology.BrainDNA.BrainConnectorEndToEndSemanticDepth as EndToEnd
import Ontology.BrainDNA.BrainChemistryCodecConsumer as Consumer
import Ontology.BrainDNA.BrainAtomicChemistryHandoff as Handoff
import Ontology.BrainDNA.PacketCodecBridge as Bridge
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)

------------------------------------------------------------------------
-- Bounded downstream consumer/law surface over the current representation
-- consumer semantics chain.
--
-- This remains theorem-thin and non-claiming. It packages exact/coherence
-- witnesses over already-landed representation, semantic-depth, semantic-law,
-- consumer-semantic, and chemistry/handoff-facing surfaces.

record BrainRepresentationConsumerLawProfile (n : Nat) : Set₁ where
  constructor mkBrainRepresentationConsumerLawProfile
  field
    representationSemantics : Map.BrainDnaRepresentationSemantics n
    semanticDepth : SemDepth.BrainRepresentationSemanticDepthProfile n
    semanticLaw : SemLaw.BrainRepresentationSemanticLawProfile n
    consumerSemantics : ConsumerSem.BrainRepresentationConsumerProfile n
    endToEnd : EndToEnd.BrainConnectorEndToEndSemanticProfile n
    order : ScanOrder
    width : Nat
    encodedAdmissibility : Bool
    emittedAdmissibility : Bool
    recoveryBoundary : Nat
    visualClass : Visual.BrainVisualFormConstant

brainRepresentationConsumerLawProfile :
  ∀ {n} → BrainState n → Region.BrainRegion → BrainRepresentationConsumerLawProfile n
brainRepresentationConsumerLawProfile st r =
  mkBrainRepresentationConsumerLawProfile
    (Map.representationSemanticsOf st r)
    (SemDepth.brainRepresentationSemanticDepthProfile st r)
    (SemLaw.brainRepresentationSemanticLawProfile st r)
    (ConsumerSem.brainRepresentationConsumerProfile st r)
    (EndToEnd.brainConnectorEndToEndSemanticProfile st r)
    (ConsumerSem.BrainRepresentationConsumerProfile.order
      (ConsumerSem.brainRepresentationConsumerProfile st r))
    (ConsumerSem.BrainRepresentationConsumerProfile.width
      (ConsumerSem.brainRepresentationConsumerProfile st r))
    (ConsumerSem.BrainRepresentationConsumerProfile.encodedAdmissibility
      (ConsumerSem.brainRepresentationConsumerProfile st r))
    (ConsumerSem.BrainRepresentationConsumerProfile.emittedAdmissibility
      (ConsumerSem.brainRepresentationConsumerProfile st r))
    (ConsumerSem.BrainRepresentationConsumerProfile.recoveryBoundary
      (ConsumerSem.brainRepresentationConsumerProfile st r))
    (ConsumerSem.BrainRepresentationConsumerProfile.visualClass
      (ConsumerSem.brainRepresentationConsumerProfile st r))

consumerLawOrderMatchesConsumerSemantics :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerLawProfile.order
    (brainRepresentationConsumerLawProfile st r)
    ≡
  ConsumerSem.BrainRepresentationConsumerProfile.order
    (ConsumerSem.brainRepresentationConsumerProfile st r)
consumerLawOrderMatchesConsumerSemantics st r = refl

consumerLawOrderMatchesSemanticLaw :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerLawProfile.order
    (brainRepresentationConsumerLawProfile st r)
    ≡
  SemLaw.BrainRepresentationSemanticLawProfile.order
    (SemLaw.brainRepresentationSemanticLawProfile st r)
consumerLawOrderMatchesSemanticLaw st r = refl

consumerLawOrderMatchesEndToEnd :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerLawProfile.order
    (brainRepresentationConsumerLawProfile st r)
    ≡
  EndToEnd.BrainConnectorEndToEndSemanticProfile.order
    (EndToEnd.brainConnectorEndToEndSemanticProfile st r)
consumerLawOrderMatchesEndToEnd st r = refl

consumerLawOrderLineMajor :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerLawProfile.order
    (brainRepresentationConsumerLawProfile st r)
    ≡
  lineMajor
consumerLawOrderLineMajor st r =
  ConsumerSem.consumerOrderLineMajor st r

consumerLawWidthMatchesConsumerSemantics :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerLawProfile.width
    (brainRepresentationConsumerLawProfile st r)
    ≡
  ConsumerSem.BrainRepresentationConsumerProfile.width
    (ConsumerSem.brainRepresentationConsumerProfile st r)
consumerLawWidthMatchesConsumerSemantics st r = refl

consumerLawWidthMatchesSemanticLaw :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerLawProfile.width
    (brainRepresentationConsumerLawProfile st r)
    ≡
  SemLaw.BrainRepresentationSemanticLawProfile.width
    (SemLaw.brainRepresentationSemanticLawProfile st r)
consumerLawWidthMatchesSemanticLaw st r = refl

consumerLawWidthMatchesEndToEnd :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerLawProfile.width
    (brainRepresentationConsumerLawProfile st r)
    ≡
  EndToEnd.BrainConnectorEndToEndSemanticProfile.width
    (EndToEnd.brainConnectorEndToEndSemanticProfile st r)
consumerLawWidthMatchesEndToEnd st r = refl

consumerLawWidthExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerLawProfile.width
    (brainRepresentationConsumerLawProfile st r)
    ≡
  n
consumerLawWidthExact st r =
  ConsumerSem.consumerWidthExact st r

consumerLawEncodedAdmissibilityMatchesConsumerSemantics :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerLawProfile.encodedAdmissibility
    (brainRepresentationConsumerLawProfile st r)
    ≡
  ConsumerSem.BrainRepresentationConsumerProfile.encodedAdmissibility
    (ConsumerSem.brainRepresentationConsumerProfile st r)
consumerLawEncodedAdmissibilityMatchesConsumerSemantics st r = refl

consumerLawEncodedAdmissibilityMatchesRepresentation :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerLawProfile.encodedAdmissibility
    (brainRepresentationConsumerLawProfile st r)
    ≡
  Bridge.packetAdmissibility
    (Map.BrainDnaRepresentation.packet
      (Map.BrainDnaRepresentationSemantics.representation
        (Map.representationSemanticsOf st r)))
consumerLawEncodedAdmissibilityMatchesRepresentation st r =
  ConsumerSem.consumerEncodedAdmissibilityMatchesRepresentation st r

consumerLawEmittedAdmissibilityMatchesConsumerSemantics :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerLawProfile.emittedAdmissibility
    (brainRepresentationConsumerLawProfile st r)
    ≡
  ConsumerSem.BrainRepresentationConsumerProfile.emittedAdmissibility
    (ConsumerSem.brainRepresentationConsumerProfile st r)
consumerLawEmittedAdmissibilityMatchesConsumerSemantics st r = refl

consumerLawEmittedAdmissibilityMatchesSemanticLaw :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerLawProfile.emittedAdmissibility
    (brainRepresentationConsumerLawProfile st r)
    ≡
  SemLaw.BrainRepresentationSemanticLawProfile.emittedAdmissibility
    (SemLaw.brainRepresentationSemanticLawProfile st r)
consumerLawEmittedAdmissibilityMatchesSemanticLaw st r = refl

consumerLawEmittedAdmissibilityMatchesChemistryConsumer :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerLawProfile.emittedAdmissibility
    (brainRepresentationConsumerLawProfile st r)
    ≡
  Consumer.BrainChemistryCodecConsumerProfile.emittedAdmissibility
    (Consumer.brainChemistryCodecConsumerProfile st)
consumerLawEmittedAdmissibilityMatchesChemistryConsumer st r =
  ConsumerSem.consumerEmittedAdmissibilityMatchesChemistryConsumer st r

consumerLawRecoveryMatchesConsumerSemantics :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerLawProfile.recoveryBoundary
    (brainRepresentationConsumerLawProfile st r)
    ≡
  ConsumerSem.BrainRepresentationConsumerProfile.recoveryBoundary
    (ConsumerSem.brainRepresentationConsumerProfile st r)
consumerLawRecoveryMatchesConsumerSemantics st r = refl

consumerLawRecoveryMatchesSemanticLaw :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerLawProfile.recoveryBoundary
    (brainRepresentationConsumerLawProfile st r)
    ≡
  SemLaw.BrainRepresentationSemanticLawProfile.recoveryBoundary
    (SemLaw.brainRepresentationSemanticLawProfile st r)
consumerLawRecoveryMatchesSemanticLaw st r = refl

consumerLawRecoveryMatchesEndToEnd :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerLawProfile.recoveryBoundary
    (brainRepresentationConsumerLawProfile st r)
    ≡
  EndToEnd.BrainConnectorEndToEndSemanticProfile.recoveryBoundary
    (EndToEnd.brainConnectorEndToEndSemanticProfile st r)
consumerLawRecoveryMatchesEndToEnd st r = refl

consumerLawRecoveryExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerLawProfile.recoveryBoundary
    (brainRepresentationConsumerLawProfile st r)
    ≡
  3
consumerLawRecoveryExact st r =
  ConsumerSem.consumerRecoveryExact st r

consumerLawRecoveryMatchesHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerLawProfile.recoveryBoundary
    (brainRepresentationConsumerLawProfile st r)
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.recoveryBoundary
    (Handoff.brainAtomicChemistryHandoffProfileOf st)
consumerLawRecoveryMatchesHandoff st r =
  ConsumerSem.consumerRecoveryMatchesHandoff st r

consumerLawVisualClassMatchesConsumerSemantics :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerLawProfile.visualClass
    (brainRepresentationConsumerLawProfile st r)
    ≡
  ConsumerSem.BrainRepresentationConsumerProfile.visualClass
    (ConsumerSem.brainRepresentationConsumerProfile st r)
consumerLawVisualClassMatchesConsumerSemantics st r = refl

consumerLawVisualClassMatchesSemanticLaw :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationConsumerLawProfile.visualClass
    (brainRepresentationConsumerLawProfile st r)
    ≡
  SemLaw.BrainRepresentationSemanticLawProfile.visualClass
    (SemLaw.brainRepresentationSemanticLawProfile st r)
consumerLawVisualClassMatchesSemanticLaw st r = refl

record BrainRepresentationConsumerLawSurface : Setω where
  field
    representationMap : Map.BrainDnaRepresentationMapSurface
    transportLaws : Transport.BrainRepresentationTransportLawSurface
    semanticDepth : SemDepth.BrainRepresentationSemanticDepthSurface
    semanticLaws : SemLaw.BrainRepresentationSemanticLawSurface
    consumerSemantics : ConsumerSem.BrainRepresentationConsumerSemanticSurface
    consumerLawProfile :
      ∀ {n} → BrainState n → Region.BrainRegion → BrainRepresentationConsumerLawProfile n

brainRepresentationConsumerLawSurface : BrainRepresentationConsumerLawSurface
brainRepresentationConsumerLawSurface = record
  { representationMap = Map.brainDnaRepresentationMapSurface
  ; transportLaws = Transport.brainRepresentationTransportLawSurface
  ; semanticDepth = SemDepth.brainRepresentationSemanticDepthSurface
  ; semanticLaws = SemLaw.brainRepresentationSemanticLawSurface
  ; consumerSemantics = ConsumerSem.brainRepresentationConsumerSemanticSurface
  ; consumerLawProfile = brainRepresentationConsumerLawProfile
  }
