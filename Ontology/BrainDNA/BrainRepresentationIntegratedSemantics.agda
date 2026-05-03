module Ontology.BrainDNA.BrainRepresentationIntegratedSemantics where

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
import Ontology.BrainDNA.BrainRepresentationConsumerLaws as ConsumerLaw
import Ontology.BrainDNA.BrainConnectorEndToEndSemanticDepth as EndToEnd
import Ontology.BrainDNA.BrainChemistryCodecConsumer as Consumer
import Ontology.BrainDNA.BrainAtomicChemistryHandoff as Handoff
import Ontology.BrainDNA.PacketCodecBridge as Bridge
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)

------------------------------------------------------------------------
-- Bounded integrated semantics over the current representation consumer
-- chain.
--
-- This remains theorem-thin and non-claiming. It packages the current
-- representation, transport, semantic-depth, semantic-law,
-- consumer-semantic, and consumer-law surfaces into one integrated profile
-- with exact/coherence witnesses over order/width/admissibility/recovery/
-- theme alignment.

record BrainRepresentationIntegratedProfile (n : Nat) : Set₁ where
  constructor mkBrainRepresentationIntegratedProfile
  field
    representationSemantics : Map.BrainDnaRepresentationSemantics n
    transportProfile : Transport.BrainRepresentationTransportProfile n
    semanticDepth : SemDepth.BrainRepresentationSemanticDepthProfile n
    semanticLaw : SemLaw.BrainRepresentationSemanticLawProfile n
    consumerSemantics : ConsumerSem.BrainRepresentationConsumerProfile n
    consumerLaw : ConsumerLaw.BrainRepresentationConsumerLawProfile n
    endToEnd : EndToEnd.BrainConnectorEndToEndSemanticProfile n
    order : ScanOrder
    width : Nat
    encodedAdmissibility : Bool
    emittedAdmissibility : Bool
    recoveryBoundary : Nat
    visualClass : Visual.BrainVisualFormConstant

brainRepresentationIntegratedProfile :
  ∀ {n} → BrainState n → Region.BrainRegion → BrainRepresentationIntegratedProfile n
brainRepresentationIntegratedProfile st r =
  mkBrainRepresentationIntegratedProfile
    (Map.representationSemanticsOf st r)
    (Transport.representationTransportProfileOf st r)
    (SemDepth.brainRepresentationSemanticDepthProfile st r)
    (SemLaw.brainRepresentationSemanticLawProfile st r)
    (ConsumerSem.brainRepresentationConsumerProfile st r)
    (ConsumerLaw.brainRepresentationConsumerLawProfile st r)
    (EndToEnd.brainConnectorEndToEndSemanticProfile st r)
    (ConsumerLaw.BrainRepresentationConsumerLawProfile.order
      (ConsumerLaw.brainRepresentationConsumerLawProfile st r))
    (ConsumerLaw.BrainRepresentationConsumerLawProfile.width
      (ConsumerLaw.brainRepresentationConsumerLawProfile st r))
    (ConsumerLaw.BrainRepresentationConsumerLawProfile.encodedAdmissibility
      (ConsumerLaw.brainRepresentationConsumerLawProfile st r))
    (ConsumerLaw.BrainRepresentationConsumerLawProfile.emittedAdmissibility
      (ConsumerLaw.brainRepresentationConsumerLawProfile st r))
    (ConsumerLaw.BrainRepresentationConsumerLawProfile.recoveryBoundary
      (ConsumerLaw.brainRepresentationConsumerLawProfile st r))
    (ConsumerLaw.BrainRepresentationConsumerLawProfile.visualClass
      (ConsumerLaw.brainRepresentationConsumerLawProfile st r))

integratedOrderMatchesConsumerLaw :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedProfile.order
    (brainRepresentationIntegratedProfile st r)
    ≡
  ConsumerLaw.BrainRepresentationConsumerLawProfile.order
    (ConsumerLaw.brainRepresentationConsumerLawProfile st r)
integratedOrderMatchesConsumerLaw st r = refl

integratedOrderMatchesSemanticLaw :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedProfile.order
    (brainRepresentationIntegratedProfile st r)
    ≡
  SemLaw.BrainRepresentationSemanticLawProfile.order
    (SemLaw.brainRepresentationSemanticLawProfile st r)
integratedOrderMatchesSemanticLaw st r = refl

integratedOrderMatchesEndToEnd :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedProfile.order
    (brainRepresentationIntegratedProfile st r)
    ≡
  EndToEnd.BrainConnectorEndToEndSemanticProfile.order
    (EndToEnd.brainConnectorEndToEndSemanticProfile st r)
integratedOrderMatchesEndToEnd st r = refl

integratedOrderLineMajor :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedProfile.order
    (brainRepresentationIntegratedProfile st r)
    ≡
  lineMajor
integratedOrderLineMajor st r =
  ConsumerLaw.consumerLawOrderLineMajor st r

integratedWidthMatchesConsumerLaw :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedProfile.width
    (brainRepresentationIntegratedProfile st r)
    ≡
  ConsumerLaw.BrainRepresentationConsumerLawProfile.width
    (ConsumerLaw.brainRepresentationConsumerLawProfile st r)
integratedWidthMatchesConsumerLaw st r = refl

integratedWidthMatchesSemanticLaw :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedProfile.width
    (brainRepresentationIntegratedProfile st r)
    ≡
  SemLaw.BrainRepresentationSemanticLawProfile.width
    (SemLaw.brainRepresentationSemanticLawProfile st r)
integratedWidthMatchesSemanticLaw st r = refl

integratedWidthMatchesEndToEnd :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedProfile.width
    (brainRepresentationIntegratedProfile st r)
    ≡
  EndToEnd.BrainConnectorEndToEndSemanticProfile.width
    (EndToEnd.brainConnectorEndToEndSemanticProfile st r)
integratedWidthMatchesEndToEnd st r = refl

integratedWidthExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedProfile.width
    (brainRepresentationIntegratedProfile st r)
    ≡
  n
integratedWidthExact st r =
  ConsumerLaw.consumerLawWidthExact st r

integratedEncodedAdmissibilityMatchesConsumerLaw :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedProfile.encodedAdmissibility
    (brainRepresentationIntegratedProfile st r)
    ≡
  ConsumerLaw.BrainRepresentationConsumerLawProfile.encodedAdmissibility
    (ConsumerLaw.brainRepresentationConsumerLawProfile st r)
integratedEncodedAdmissibilityMatchesConsumerLaw st r = refl

integratedEncodedAdmissibilityMatchesRepresentation :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedProfile.encodedAdmissibility
    (brainRepresentationIntegratedProfile st r)
    ≡
  Bridge.packetAdmissibility
    (Map.BrainDnaRepresentation.packet
      (Map.BrainDnaRepresentationSemantics.representation
        (Map.representationSemanticsOf st r)))
integratedEncodedAdmissibilityMatchesRepresentation st r =
  ConsumerLaw.consumerLawEncodedAdmissibilityMatchesRepresentation st r

integratedEmittedAdmissibilityMatchesConsumerLaw :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedProfile.emittedAdmissibility
    (brainRepresentationIntegratedProfile st r)
    ≡
  ConsumerLaw.BrainRepresentationConsumerLawProfile.emittedAdmissibility
    (ConsumerLaw.brainRepresentationConsumerLawProfile st r)
integratedEmittedAdmissibilityMatchesConsumerLaw st r = refl

integratedEmittedAdmissibilityMatchesSemanticLaw :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedProfile.emittedAdmissibility
    (brainRepresentationIntegratedProfile st r)
    ≡
  SemLaw.BrainRepresentationSemanticLawProfile.emittedAdmissibility
    (SemLaw.brainRepresentationSemanticLawProfile st r)
integratedEmittedAdmissibilityMatchesSemanticLaw st r = refl

integratedEmittedAdmissibilityMatchesChemistryConsumer :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedProfile.emittedAdmissibility
    (brainRepresentationIntegratedProfile st r)
    ≡
  Consumer.BrainChemistryCodecConsumerProfile.emittedAdmissibility
    (Consumer.brainChemistryCodecConsumerProfile st)
integratedEmittedAdmissibilityMatchesChemistryConsumer st r =
  ConsumerLaw.consumerLawEmittedAdmissibilityMatchesChemistryConsumer st r

integratedRecoveryMatchesConsumerLaw :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedProfile.recoveryBoundary
    (brainRepresentationIntegratedProfile st r)
    ≡
  ConsumerLaw.BrainRepresentationConsumerLawProfile.recoveryBoundary
    (ConsumerLaw.brainRepresentationConsumerLawProfile st r)
integratedRecoveryMatchesConsumerLaw st r = refl

integratedRecoveryMatchesSemanticLaw :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedProfile.recoveryBoundary
    (brainRepresentationIntegratedProfile st r)
    ≡
  SemLaw.BrainRepresentationSemanticLawProfile.recoveryBoundary
    (SemLaw.brainRepresentationSemanticLawProfile st r)
integratedRecoveryMatchesSemanticLaw st r = refl

integratedRecoveryMatchesEndToEnd :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedProfile.recoveryBoundary
    (brainRepresentationIntegratedProfile st r)
    ≡
  EndToEnd.BrainConnectorEndToEndSemanticProfile.recoveryBoundary
    (EndToEnd.brainConnectorEndToEndSemanticProfile st r)
integratedRecoveryMatchesEndToEnd st r = refl

integratedRecoveryExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedProfile.recoveryBoundary
    (brainRepresentationIntegratedProfile st r)
    ≡
  3
integratedRecoveryExact st r =
  ConsumerLaw.consumerLawRecoveryExact st r

integratedRecoveryMatchesHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedProfile.recoveryBoundary
    (brainRepresentationIntegratedProfile st r)
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.recoveryBoundary
    (Handoff.brainAtomicChemistryHandoffProfileOf st)
integratedRecoveryMatchesHandoff st r =
  ConsumerLaw.consumerLawRecoveryMatchesHandoff st r

integratedVisualClassMatchesConsumerLaw :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedProfile.visualClass
    (brainRepresentationIntegratedProfile st r)
    ≡
  ConsumerLaw.BrainRepresentationConsumerLawProfile.visualClass
    (ConsumerLaw.brainRepresentationConsumerLawProfile st r)
integratedVisualClassMatchesConsumerLaw st r = refl

integratedVisualClassMatchesSemanticLaw :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedProfile.visualClass
    (brainRepresentationIntegratedProfile st r)
    ≡
  SemLaw.BrainRepresentationSemanticLawProfile.visualClass
    (SemLaw.brainRepresentationSemanticLawProfile st r)
integratedVisualClassMatchesSemanticLaw st r = refl

record BrainRepresentationIntegratedSemanticSurface : Setω where
  field
    representationMap : Map.BrainDnaRepresentationMapSurface
    transportLaws : Transport.BrainRepresentationTransportLawSurface
    semanticDepth : SemDepth.BrainRepresentationSemanticDepthSurface
    semanticLaws : SemLaw.BrainRepresentationSemanticLawSurface
    consumerSemantics : ConsumerSem.BrainRepresentationConsumerSemanticSurface
    consumerLaws : ConsumerLaw.BrainRepresentationConsumerLawSurface
    integratedProfile :
      ∀ {n} → BrainState n → Region.BrainRegion → BrainRepresentationIntegratedProfile n

brainRepresentationIntegratedSemanticSurface : BrainRepresentationIntegratedSemanticSurface
brainRepresentationIntegratedSemanticSurface = record
  { representationMap = Map.brainDnaRepresentationMapSurface
  ; transportLaws = Transport.brainRepresentationTransportLawSurface
  ; semanticDepth = SemDepth.brainRepresentationSemanticDepthSurface
  ; semanticLaws = SemLaw.brainRepresentationSemanticLawSurface
  ; consumerSemantics = ConsumerSem.brainRepresentationConsumerSemanticSurface
  ; consumerLaws = ConsumerLaw.brainRepresentationConsumerLawSurface
  ; integratedProfile = brainRepresentationIntegratedProfile
  }
