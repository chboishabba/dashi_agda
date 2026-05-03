module Ontology.BrainDNA.BrainRepresentationIntegratedLaws where

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
import Ontology.BrainDNA.BrainRepresentationIntegratedSemantics as Integrated
import Ontology.BrainDNA.BrainConnectorEndToEndSemanticDepth as EndToEnd
import Ontology.BrainDNA.BrainChemistryCodecConsumer as Consumer
import Ontology.BrainDNA.BrainAtomicChemistryHandoff as Handoff
import Ontology.BrainDNA.PacketCodecBridge as Bridge
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)

------------------------------------------------------------------------
-- Bounded integrated-law surface over the current representation
-- integration chain.
--
-- This remains theorem-thin and non-claiming. It packages exact/coherence
-- witnesses over the already-landed representation, transport,
-- semantic-depth, semantic-law, consumer, and integrated semantic owners.

record BrainRepresentationIntegratedLawProfile (n : Nat) : Set₁ where
  constructor mkBrainRepresentationIntegratedLawProfile
  field
    representationSemantics : Map.BrainDnaRepresentationSemantics n
    transportProfile : Transport.BrainRepresentationTransportProfile n
    semanticDepth : SemDepth.BrainRepresentationSemanticDepthProfile n
    semanticLaw : SemLaw.BrainRepresentationSemanticLawProfile n
    consumerSemantics : ConsumerSem.BrainRepresentationConsumerProfile n
    consumerLaw : ConsumerLaw.BrainRepresentationConsumerLawProfile n
    integratedSemantics : Integrated.BrainRepresentationIntegratedProfile n
    endToEnd : EndToEnd.BrainConnectorEndToEndSemanticProfile n
    order : ScanOrder
    width : Nat
    encodedAdmissibility : Bool
    emittedAdmissibility : Bool
    recoveryBoundary : Nat
    visualClass : Visual.BrainVisualFormConstant

brainRepresentationIntegratedLawProfile :
  ∀ {n} → BrainState n → Region.BrainRegion → BrainRepresentationIntegratedLawProfile n
brainRepresentationIntegratedLawProfile st r =
  mkBrainRepresentationIntegratedLawProfile
    (Map.representationSemanticsOf st r)
    (Transport.representationTransportProfileOf st r)
    (SemDepth.brainRepresentationSemanticDepthProfile st r)
    (SemLaw.brainRepresentationSemanticLawProfile st r)
    (ConsumerSem.brainRepresentationConsumerProfile st r)
    (ConsumerLaw.brainRepresentationConsumerLawProfile st r)
    (Integrated.brainRepresentationIntegratedProfile st r)
    (EndToEnd.brainConnectorEndToEndSemanticProfile st r)
    (Integrated.BrainRepresentationIntegratedProfile.order
      (Integrated.brainRepresentationIntegratedProfile st r))
    (Integrated.BrainRepresentationIntegratedProfile.width
      (Integrated.brainRepresentationIntegratedProfile st r))
    (Integrated.BrainRepresentationIntegratedProfile.encodedAdmissibility
      (Integrated.brainRepresentationIntegratedProfile st r))
    (Integrated.BrainRepresentationIntegratedProfile.emittedAdmissibility
      (Integrated.brainRepresentationIntegratedProfile st r))
    (Integrated.BrainRepresentationIntegratedProfile.recoveryBoundary
      (Integrated.brainRepresentationIntegratedProfile st r))
    (Integrated.BrainRepresentationIntegratedProfile.visualClass
      (Integrated.brainRepresentationIntegratedProfile st r))

integratedLawOrderMatchesIntegratedSemantics :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedLawProfile.order
    (brainRepresentationIntegratedLawProfile st r)
    ≡
  Integrated.BrainRepresentationIntegratedProfile.order
    (Integrated.brainRepresentationIntegratedProfile st r)
integratedLawOrderMatchesIntegratedSemantics st r = refl

integratedLawOrderMatchesConsumerLaw :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedLawProfile.order
    (brainRepresentationIntegratedLawProfile st r)
    ≡
  ConsumerLaw.BrainRepresentationConsumerLawProfile.order
    (ConsumerLaw.brainRepresentationConsumerLawProfile st r)
integratedLawOrderMatchesConsumerLaw st r = refl

integratedLawOrderMatchesSemanticLaw :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedLawProfile.order
    (brainRepresentationIntegratedLawProfile st r)
    ≡
  SemLaw.BrainRepresentationSemanticLawProfile.order
    (SemLaw.brainRepresentationSemanticLawProfile st r)
integratedLawOrderMatchesSemanticLaw st r = refl

integratedLawOrderMatchesEndToEnd :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedLawProfile.order
    (brainRepresentationIntegratedLawProfile st r)
    ≡
  EndToEnd.BrainConnectorEndToEndSemanticProfile.order
    (EndToEnd.brainConnectorEndToEndSemanticProfile st r)
integratedLawOrderMatchesEndToEnd st r = refl

integratedLawOrderLineMajor :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedLawProfile.order
    (brainRepresentationIntegratedLawProfile st r)
    ≡
  lineMajor
integratedLawOrderLineMajor st r =
  Integrated.integratedOrderLineMajor st r

integratedLawWidthMatchesIntegratedSemantics :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedLawProfile.width
    (brainRepresentationIntegratedLawProfile st r)
    ≡
  Integrated.BrainRepresentationIntegratedProfile.width
    (Integrated.brainRepresentationIntegratedProfile st r)
integratedLawWidthMatchesIntegratedSemantics st r = refl

integratedLawWidthMatchesConsumerLaw :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedLawProfile.width
    (brainRepresentationIntegratedLawProfile st r)
    ≡
  ConsumerLaw.BrainRepresentationConsumerLawProfile.width
    (ConsumerLaw.brainRepresentationConsumerLawProfile st r)
integratedLawWidthMatchesConsumerLaw st r = refl

integratedLawWidthMatchesSemanticLaw :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedLawProfile.width
    (brainRepresentationIntegratedLawProfile st r)
    ≡
  SemLaw.BrainRepresentationSemanticLawProfile.width
    (SemLaw.brainRepresentationSemanticLawProfile st r)
integratedLawWidthMatchesSemanticLaw st r = refl

integratedLawWidthMatchesEndToEnd :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedLawProfile.width
    (brainRepresentationIntegratedLawProfile st r)
    ≡
  EndToEnd.BrainConnectorEndToEndSemanticProfile.width
    (EndToEnd.brainConnectorEndToEndSemanticProfile st r)
integratedLawWidthMatchesEndToEnd st r = refl

integratedLawWidthExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedLawProfile.width
    (brainRepresentationIntegratedLawProfile st r)
    ≡
  n
integratedLawWidthExact st r =
  Integrated.integratedWidthExact st r

integratedLawEncodedAdmissibilityMatchesIntegratedSemantics :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedLawProfile.encodedAdmissibility
    (brainRepresentationIntegratedLawProfile st r)
    ≡
  Integrated.BrainRepresentationIntegratedProfile.encodedAdmissibility
    (Integrated.brainRepresentationIntegratedProfile st r)
integratedLawEncodedAdmissibilityMatchesIntegratedSemantics st r = refl

integratedLawEncodedAdmissibilityMatchesRepresentation :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedLawProfile.encodedAdmissibility
    (brainRepresentationIntegratedLawProfile st r)
    ≡
  Bridge.packetAdmissibility
    (Map.BrainDnaRepresentation.packet
      (Map.BrainDnaRepresentationSemantics.representation
        (Map.representationSemanticsOf st r)))
integratedLawEncodedAdmissibilityMatchesRepresentation st r =
  Integrated.integratedEncodedAdmissibilityMatchesRepresentation st r

integratedLawEmittedAdmissibilityMatchesIntegratedSemantics :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedLawProfile.emittedAdmissibility
    (brainRepresentationIntegratedLawProfile st r)
    ≡
  Integrated.BrainRepresentationIntegratedProfile.emittedAdmissibility
    (Integrated.brainRepresentationIntegratedProfile st r)
integratedLawEmittedAdmissibilityMatchesIntegratedSemantics st r = refl

integratedLawEmittedAdmissibilityMatchesConsumerLaw :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedLawProfile.emittedAdmissibility
    (brainRepresentationIntegratedLawProfile st r)
    ≡
  ConsumerLaw.BrainRepresentationConsumerLawProfile.emittedAdmissibility
    (ConsumerLaw.brainRepresentationConsumerLawProfile st r)
integratedLawEmittedAdmissibilityMatchesConsumerLaw st r = refl

integratedLawEmittedAdmissibilityMatchesChemistryConsumer :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedLawProfile.emittedAdmissibility
    (brainRepresentationIntegratedLawProfile st r)
    ≡
  Consumer.BrainChemistryCodecConsumerProfile.emittedAdmissibility
    (Consumer.brainChemistryCodecConsumerProfile st)
integratedLawEmittedAdmissibilityMatchesChemistryConsumer st r =
  Integrated.integratedEmittedAdmissibilityMatchesChemistryConsumer st r

integratedLawRecoveryMatchesIntegratedSemantics :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedLawProfile.recoveryBoundary
    (brainRepresentationIntegratedLawProfile st r)
    ≡
  Integrated.BrainRepresentationIntegratedProfile.recoveryBoundary
    (Integrated.brainRepresentationIntegratedProfile st r)
integratedLawRecoveryMatchesIntegratedSemantics st r = refl

integratedLawRecoveryMatchesConsumerLaw :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedLawProfile.recoveryBoundary
    (brainRepresentationIntegratedLawProfile st r)
    ≡
  ConsumerLaw.BrainRepresentationConsumerLawProfile.recoveryBoundary
    (ConsumerLaw.brainRepresentationConsumerLawProfile st r)
integratedLawRecoveryMatchesConsumerLaw st r = refl

integratedLawRecoveryMatchesSemanticLaw :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedLawProfile.recoveryBoundary
    (brainRepresentationIntegratedLawProfile st r)
    ≡
  SemLaw.BrainRepresentationSemanticLawProfile.recoveryBoundary
    (SemLaw.brainRepresentationSemanticLawProfile st r)
integratedLawRecoveryMatchesSemanticLaw st r = refl

integratedLawRecoveryMatchesEndToEnd :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedLawProfile.recoveryBoundary
    (brainRepresentationIntegratedLawProfile st r)
    ≡
  EndToEnd.BrainConnectorEndToEndSemanticProfile.recoveryBoundary
    (EndToEnd.brainConnectorEndToEndSemanticProfile st r)
integratedLawRecoveryMatchesEndToEnd st r = refl

integratedLawRecoveryExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedLawProfile.recoveryBoundary
    (brainRepresentationIntegratedLawProfile st r)
    ≡
  3
integratedLawRecoveryExact st r =
  Integrated.integratedRecoveryExact st r

integratedLawRecoveryMatchesHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedLawProfile.recoveryBoundary
    (brainRepresentationIntegratedLawProfile st r)
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.recoveryBoundary
    (Handoff.brainAtomicChemistryHandoffProfileOf st)
integratedLawRecoveryMatchesHandoff st r =
  Integrated.integratedRecoveryMatchesHandoff st r

integratedLawVisualClassMatchesIntegratedSemantics :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedLawProfile.visualClass
    (brainRepresentationIntegratedLawProfile st r)
    ≡
  Integrated.BrainRepresentationIntegratedProfile.visualClass
    (Integrated.brainRepresentationIntegratedProfile st r)
integratedLawVisualClassMatchesIntegratedSemantics st r = refl

integratedLawVisualClassMatchesConsumerLaw :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedLawProfile.visualClass
    (brainRepresentationIntegratedLawProfile st r)
    ≡
  ConsumerLaw.BrainRepresentationConsumerLawProfile.visualClass
    (ConsumerLaw.brainRepresentationConsumerLawProfile st r)
integratedLawVisualClassMatchesConsumerLaw st r = refl

integratedLawVisualClassMatchesSemanticLaw :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationIntegratedLawProfile.visualClass
    (brainRepresentationIntegratedLawProfile st r)
    ≡
  SemLaw.BrainRepresentationSemanticLawProfile.visualClass
    (SemLaw.brainRepresentationSemanticLawProfile st r)
integratedLawVisualClassMatchesSemanticLaw st r = refl

record BrainRepresentationIntegratedLawSurface : Setω where
  field
    representationMap : Map.BrainDnaRepresentationMapSurface
    transportLaws : Transport.BrainRepresentationTransportLawSurface
    semanticDepth : SemDepth.BrainRepresentationSemanticDepthSurface
    semanticLaws : SemLaw.BrainRepresentationSemanticLawSurface
    consumerSemantics : ConsumerSem.BrainRepresentationConsumerSemanticSurface
    consumerLaws : ConsumerLaw.BrainRepresentationConsumerLawSurface
    integratedSemantics : Integrated.BrainRepresentationIntegratedSemanticSurface
    integratedLawProfile :
      ∀ {n} → BrainState n → Region.BrainRegion → BrainRepresentationIntegratedLawProfile n

brainRepresentationIntegratedLawSurface : BrainRepresentationIntegratedLawSurface
brainRepresentationIntegratedLawSurface = record
  { representationMap = Map.brainDnaRepresentationMapSurface
  ; transportLaws = Transport.brainRepresentationTransportLawSurface
  ; semanticDepth = SemDepth.brainRepresentationSemanticDepthSurface
  ; semanticLaws = SemLaw.brainRepresentationSemanticLawSurface
  ; consumerSemantics = ConsumerSem.brainRepresentationConsumerSemanticSurface
  ; consumerLaws = ConsumerLaw.brainRepresentationConsumerLawSurface
  ; integratedSemantics = Integrated.brainRepresentationIntegratedSemanticSurface
  ; integratedLawProfile = brainRepresentationIntegratedLawProfile
  }
