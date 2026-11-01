module Ontology.BrainDNA.BrainRepresentationTransportLaws where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
import Ontology.Brain.BrainRegionAutomatonSurface as Region
import Ontology.Brain.BrainVisualFormConstantSurface as Visual
import Ontology.BrainDNA.BrainDnaRepresentationMap as Map
import Ontology.BrainDNA.BrainThemeConnectorSurface as Theme
import Ontology.BrainDNA.BrainConnectorSemanticDepth as Depth
import Ontology.BrainDNA.BrainChemistryCodecConsumer as Consumer
import Ontology.BrainDNA.BrainAtomicChemistryHandoff as Handoff
import Ontology.BrainDNA.PacketCodecBridge as Bridge
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)

symEq : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
symEq refl = refl

transEq : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
transEq refl q = q

------------------------------------------------------------------------
-- Bounded end-to-end transport laws over the current brain->DNA
-- representation chain.
--
-- This stays theorem-thin and non-claiming: it only packages exact
-- profile/order/width/admissibility/recovery-boundary coherence over the
-- already-landed owners. It does not claim realistic biology or global
-- semantics.

record BrainRepresentationTransportProfile (n : Nat) : Set₁ where
  constructor brainRepresentationTransportProfile
  field
    representation : Map.BrainDnaRepresentationSemantics n
    connectorDepth : Depth.BrainConnectorSemanticDepthProfile n
    chemistryConsumer : Consumer.BrainChemistryCodecConsumerProfile
    atomicHandoff : Handoff.BrainAtomicChemistryHandoffProfile n

representationTransportProfileOf :
  ∀ {n} → BrainState n → Region.BrainRegion → BrainRepresentationTransportProfile n
representationTransportProfileOf st r =
  brainRepresentationTransportProfile
    (Map.representationSemanticsOf st r)
    (Depth.brainConnectorSemanticDepthProfile st r)
    (Consumer.brainChemistryCodecConsumerProfile st)
    (Handoff.brainAtomicChemistryHandoffProfileOf st)

transportThemeOrderCompatible :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  Map.BrainDnaRepresentationSemantics.order
    (BrainRepresentationTransportProfile.representation
      (representationTransportProfileOf st r))
    ≡
  Theme.BrainThemeProfile.packetOrder
    (Theme.themeProfileOf st r)
transportThemeOrderCompatible st r =
  Map.representationSemanticsProfileOrderCompatible st r

transportOrderMatchesConnectorDepth :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  Map.BrainDnaRepresentationSemantics.order
    (BrainRepresentationTransportProfile.representation
      (representationTransportProfileOf st r))
    ≡
  Depth.BrainConnectorSemanticDepthProfile.order
    (BrainRepresentationTransportProfile.connectorDepth
      (representationTransportProfileOf st r))
transportOrderMatchesConnectorDepth st r =
  transEq
    (Map.representationOrderLineMajor st r)
    (symEq (Depth.connectorSemanticDepthOrderLineMajor st r))

transportOrderMatchesAtomicHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  Map.BrainDnaRepresentationSemantics.order
    (BrainRepresentationTransportProfile.representation
      (representationTransportProfileOf st r))
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.order
    (BrainRepresentationTransportProfile.atomicHandoff
      (representationTransportProfileOf st r))
transportOrderMatchesAtomicHandoff st r =
  transEq
    (Map.representationOrderLineMajor st r)
    (symEq (Handoff.handoffOrderLineMajor st))

transportOrderLineMajor :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  Map.BrainDnaRepresentationSemantics.order
    (BrainRepresentationTransportProfile.representation
      (representationTransportProfileOf st r))
    ≡
  lineMajor
transportOrderLineMajor st r =
  Map.representationOrderLineMajor st r

transportWidthMatchesTheme :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  Map.BrainDnaRepresentationSemantics.width
    (BrainRepresentationTransportProfile.representation
      (representationTransportProfileOf st r))
    ≡
  Visual.BrainLogPolarGeometry.radialRing
    (Theme.BrainThemeProfile.visualGeometry (Theme.themeProfileOf st r))
transportWidthMatchesTheme st r =
  symEq (Map.representationVisualWidthExact st r)

transportWidthMatchesHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  Map.BrainDnaRepresentationSemantics.width
    (BrainRepresentationTransportProfile.representation
      (representationTransportProfileOf st r))
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.width
    (BrainRepresentationTransportProfile.atomicHandoff
      (representationTransportProfileOf st r))
transportWidthMatchesHandoff st r =
  transEq
    (Map.representationSemanticsWidthExact st r)
    (symEq (Handoff.handoffWidthExact st))

transportEncodedAdmissibilityMatchesPacket :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  Map.BrainDnaRepresentationSemantics.encodedAdmissibility
    (BrainRepresentationTransportProfile.representation
      (representationTransportProfileOf st r))
    ≡
  Bridge.packetAdmissibility
    (Map.BrainDnaRepresentation.packet
      (Map.BrainDnaRepresentationSemantics.representation
        (BrainRepresentationTransportProfile.representation
          (representationTransportProfileOf st r))))
transportEncodedAdmissibilityMatchesPacket st r =
  Map.representationSemanticsEncodedAdmissibilityExact st r

transportEmittedAdmissibilityMatchesPacket :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  Map.BrainDnaRepresentationSemantics.emittedAdmissibility
    (BrainRepresentationTransportProfile.representation
      (representationTransportProfileOf st r))
    ≡
  Bridge.packetAdmissibility
    (Map.BrainDnaRepresentation.packet
      (Map.BrainDnaRepresentationSemantics.representation
        (BrainRepresentationTransportProfile.representation
          (representationTransportProfileOf st r))))
transportEmittedAdmissibilityMatchesPacket st r =
  Map.representationSemanticsEmittedAdmissibilityExact st r

transportEmittedAdmissibilityMatchesConsumer :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  Map.BrainDnaRepresentationSemantics.emittedAdmissibility
    (BrainRepresentationTransportProfile.representation
      (representationTransportProfileOf st r))
    ≡
  Consumer.BrainChemistryCodecConsumerProfile.emittedAdmissibility
    (BrainRepresentationTransportProfile.chemistryConsumer
      (representationTransportProfileOf st r))
transportEmittedAdmissibilityMatchesConsumer st r =
  transEq
    (Map.representationSemanticsEmittedAdmissibilityExact st r)
    (symEq (Consumer.consumerEmittedAdmissibilityTrue st))

transportRecoveryBoundaryExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  Depth.BrainConnectorSemanticDepthProfile.recoveryBoundary
    (BrainRepresentationTransportProfile.connectorDepth
      (representationTransportProfileOf st r))
    ≡
  3
transportRecoveryBoundaryExact st r =
  Depth.connectorSemanticDepthRecoveryBoundaryExact st r

transportRecoveryBoundaryMatchesConsumer :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  Depth.BrainConnectorSemanticDepthProfile.recoveryBoundary
    (BrainRepresentationTransportProfile.connectorDepth
      (representationTransportProfileOf st r))
    ≡
  Consumer.BrainChemistryCodecConsumerProfile.recoveryBoundary
    (BrainRepresentationTransportProfile.chemistryConsumer
      (representationTransportProfileOf st r))
transportRecoveryBoundaryMatchesConsumer st r =
  transEq
    (Depth.connectorSemanticDepthRecoveryBoundaryExact st r)
    (symEq (Consumer.consumerRecoveryBoundaryExact st))

transportRecoveryBoundaryMatchesHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  Depth.BrainConnectorSemanticDepthProfile.recoveryBoundary
    (BrainRepresentationTransportProfile.connectorDepth
      (representationTransportProfileOf st r))
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.recoveryBoundary
    (BrainRepresentationTransportProfile.atomicHandoff
      (representationTransportProfileOf st r))
transportRecoveryBoundaryMatchesHandoff st r =
  Depth.connectorSemanticDepthRecoveryBoundaryMatchesHandoff st r

record BrainRepresentationTransportLawSurface : Setω where
  field
    representationMap : Map.BrainDnaRepresentationMapSurface
    themeConnector : Theme.BrainThemeConnectorSurface
    connectorSemanticDepth : Depth.BrainConnectorSemanticDepthSurface
    chemistryConsumer : Consumer.BrainChemistryCodecConsumerSurface
    atomicHandoff : Handoff.BrainAtomicChemistryHandoffSurface
    transportProfile :
      ∀ {n} → BrainState n → Region.BrainRegion → BrainRepresentationTransportProfile n

brainRepresentationTransportLawSurface : BrainRepresentationTransportLawSurface
brainRepresentationTransportLawSurface = record
  { representationMap = Map.brainDnaRepresentationMapSurface
  ; themeConnector = Theme.brainThemeConnectorSurface
  ; connectorSemanticDepth = Depth.brainConnectorSemanticDepthSurface
  ; chemistryConsumer = Consumer.brainChemistryCodecConsumerSurface
  ; atomicHandoff = Handoff.brainAtomicChemistryHandoffSurface
  ; transportProfile = representationTransportProfileOf
  }
