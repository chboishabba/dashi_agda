module Ontology.BrainDNA.BrainRepresentationSemanticDepth where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
import Ontology.Brain.BrainRegionAutomatonSurface as Region
import Ontology.Brain.BrainVisualFormConstantSurface as Visual
import Ontology.BrainDNA.BrainDnaRepresentationMap as Map
import Ontology.BrainDNA.BrainRepresentationTransportLaws as Transport
import Ontology.BrainDNA.BrainConnectorSemanticDepth as Depth
import Ontology.BrainDNA.BrainChemistryCodecConsumer as Consumer
import Ontology.BrainDNA.BrainAtomicChemistryHandoff as Handoff
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)
import Ontology.BrainDNA.PacketCodecBridge as Bridge

------------------------------------------------------------------------
-- Bounded semantic-depth surface over the current brain->DNA
-- representation chain.
--
-- This remains theorem-thin and non-claiming. It packages the already-landed
-- representation semantics, transport profile, connector semantic depth, and
-- atomic chemistry handoff into one deeper local surface with exact/coherence
-- witnesses for profile/order/width/admissibility/recovery/handoff alignment.

record BrainRepresentationSemanticDepthProfile (n : Nat) : Set₁ where
  constructor mkBrainRepresentationSemanticDepthProfile
  field
    representationSemantics : Map.BrainDnaRepresentationSemantics n
    transportProfile : Transport.BrainRepresentationTransportProfile n
    order : ScanOrder
    width : Nat
    encodedAdmissibility : Bool
    emittedAdmissibility : Bool
    recoveryBoundary : Nat
    visualClass : Visual.BrainVisualFormConstant
    crossBand : Nat
    hamiltonian : Nat

brainRepresentationSemanticDepthProfile :
  ∀ {n} → BrainState n → Region.BrainRegion → BrainRepresentationSemanticDepthProfile n
brainRepresentationSemanticDepthProfile st r =
  mkBrainRepresentationSemanticDepthProfile
    (Map.representationSemanticsOf st r)
    (Transport.representationTransportProfileOf st r)
    (Map.BrainDnaRepresentationSemantics.order
      (Map.representationSemanticsOf st r))
    (Map.BrainDnaRepresentationSemantics.width
      (Map.representationSemanticsOf st r))
    (Map.BrainDnaRepresentationSemantics.encodedAdmissibility
      (Map.representationSemanticsOf st r))
    (Map.BrainDnaRepresentationSemantics.emittedAdmissibility
      (Map.representationSemanticsOf st r))
    (Depth.BrainConnectorSemanticDepthProfile.recoveryBoundary
      (Depth.brainConnectorSemanticDepthProfile st r))
    (Depth.BrainConnectorSemanticDepthProfile.visualClass
      (Depth.brainConnectorSemanticDepthProfile st r))
    (Depth.BrainConnectorSemanticDepthProfile.crossBand
      (Depth.brainConnectorSemanticDepthProfile st r))
    (Depth.BrainConnectorSemanticDepthProfile.hamiltonian
      (Depth.brainConnectorSemanticDepthProfile st r))

representationSemanticDepthOrderMatchesTransport :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationSemanticDepthProfile.order
    (brainRepresentationSemanticDepthProfile st r)
    ≡
  Map.BrainDnaRepresentationSemantics.order
    (Transport.BrainRepresentationTransportProfile.representation
      (Transport.representationTransportProfileOf st r))
representationSemanticDepthOrderMatchesTransport st r = refl

representationSemanticDepthOrderLineMajor :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationSemanticDepthProfile.order
    (brainRepresentationSemanticDepthProfile st r)
    ≡
  lineMajor
representationSemanticDepthOrderLineMajor st r =
  Transport.transportOrderLineMajor st r

representationSemanticDepthWidthMatchesTransport :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationSemanticDepthProfile.width
    (brainRepresentationSemanticDepthProfile st r)
    ≡
  Map.BrainDnaRepresentationSemantics.width
    (Transport.BrainRepresentationTransportProfile.representation
      (Transport.representationTransportProfileOf st r))
representationSemanticDepthWidthMatchesTransport st r = refl

representationSemanticDepthWidthExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationSemanticDepthProfile.width
    (brainRepresentationSemanticDepthProfile st r)
    ≡
  n
representationSemanticDepthWidthExact st r =
  Map.representationSemanticsWidthExact st r

representationSemanticDepthEncodedAdmissibilityMatchesTransport :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationSemanticDepthProfile.encodedAdmissibility
    (brainRepresentationSemanticDepthProfile st r)
    ≡
  Map.BrainDnaRepresentationSemantics.encodedAdmissibility
    (Transport.BrainRepresentationTransportProfile.representation
      (Transport.representationTransportProfileOf st r))
representationSemanticDepthEncodedAdmissibilityMatchesTransport st r = refl

representationSemanticDepthEncodedAdmissibilityMatchesPacket :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationSemanticDepthProfile.encodedAdmissibility
    (brainRepresentationSemanticDepthProfile st r)
    ≡
  Bridge.packetAdmissibility
    (Map.BrainDnaRepresentation.packet
      (Map.BrainDnaRepresentationSemantics.representation
        (BrainRepresentationSemanticDepthProfile.representationSemantics
          (brainRepresentationSemanticDepthProfile st r))))
representationSemanticDepthEncodedAdmissibilityMatchesPacket st r =
  Map.representationSemanticsEncodedAdmissibilityExact st r

representationSemanticDepthEmittedAdmissibilityMatchesTransport :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationSemanticDepthProfile.emittedAdmissibility
    (brainRepresentationSemanticDepthProfile st r)
    ≡
  Map.BrainDnaRepresentationSemantics.emittedAdmissibility
    (Transport.BrainRepresentationTransportProfile.representation
      (Transport.representationTransportProfileOf st r))
representationSemanticDepthEmittedAdmissibilityMatchesTransport st r = refl

representationSemanticDepthEmittedAdmissibilityMatchesHandoffChain :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationSemanticDepthProfile.emittedAdmissibility
    (brainRepresentationSemanticDepthProfile st r)
    ≡
  Consumer.BrainChemistryCodecConsumerProfile.emittedAdmissibility
    (Transport.BrainRepresentationTransportProfile.chemistryConsumer
      (Transport.representationTransportProfileOf st r))
representationSemanticDepthEmittedAdmissibilityMatchesHandoffChain st r =
  Transport.transportEmittedAdmissibilityMatchesConsumer st r

representationSemanticDepthRecoveryMatchesTransport :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationSemanticDepthProfile.recoveryBoundary
    (brainRepresentationSemanticDepthProfile st r)
    ≡
  Depth.BrainConnectorSemanticDepthProfile.recoveryBoundary
    (Transport.BrainRepresentationTransportProfile.connectorDepth
      (Transport.representationTransportProfileOf st r))
representationSemanticDepthRecoveryMatchesTransport st r = refl

representationSemanticDepthRecoveryExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationSemanticDepthProfile.recoveryBoundary
    (brainRepresentationSemanticDepthProfile st r)
    ≡
  3
representationSemanticDepthRecoveryExact st r =
  Transport.transportRecoveryBoundaryExact st r

representationSemanticDepthRecoveryMatchesHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationSemanticDepthProfile.recoveryBoundary
    (brainRepresentationSemanticDepthProfile st r)
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.recoveryBoundary
    (Handoff.brainAtomicChemistryHandoffProfileOf st)
representationSemanticDepthRecoveryMatchesHandoff st r =
  Transport.transportRecoveryBoundaryMatchesHandoff st r

representationSemanticDepthVisualClassMatchesConnectorDepth :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationSemanticDepthProfile.visualClass
    (brainRepresentationSemanticDepthProfile st r)
    ≡
  Depth.BrainConnectorSemanticDepthProfile.visualClass
    (Transport.BrainRepresentationTransportProfile.connectorDepth
      (Transport.representationTransportProfileOf st r))
representationSemanticDepthVisualClassMatchesConnectorDepth st r = refl

representationSemanticDepthCrossBandMatchesHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationSemanticDepthProfile.crossBand
    (brainRepresentationSemanticDepthProfile st r)
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.crossBand
    (Handoff.brainAtomicChemistryHandoffProfileOf st)
representationSemanticDepthCrossBandMatchesHandoff st r = refl

representationSemanticDepthHamiltonianMatchesHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainRepresentationSemanticDepthProfile.hamiltonian
    (brainRepresentationSemanticDepthProfile st r)
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.hamiltonian
    (Handoff.brainAtomicChemistryHandoffProfileOf st)
representationSemanticDepthHamiltonianMatchesHandoff st r = refl

record BrainRepresentationSemanticDepthSurface : Setω where
  field
    representationMap : Map.BrainDnaRepresentationMapSurface
    transportLaws : Transport.BrainRepresentationTransportLawSurface
    connectorSemanticDepth : Depth.BrainConnectorSemanticDepthSurface
    atomicHandoff : Handoff.BrainAtomicChemistryHandoffSurface
    semanticDepthProfile :
      ∀ {n} → BrainState n → Region.BrainRegion → BrainRepresentationSemanticDepthProfile n

brainRepresentationSemanticDepthSurface : BrainRepresentationSemanticDepthSurface
brainRepresentationSemanticDepthSurface = record
  { representationMap = Map.brainDnaRepresentationMapSurface
  ; transportLaws = Transport.brainRepresentationTransportLawSurface
  ; connectorSemanticDepth = Depth.brainConnectorSemanticDepthSurface
  ; atomicHandoff = Handoff.brainAtomicChemistryHandoffSurface
  ; semanticDepthProfile = brainRepresentationSemanticDepthProfile
  }
