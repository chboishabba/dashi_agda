module Ontology.BrainDNA.BrainConnectorEndToEndSemanticDepth where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
import Ontology.Brain.BrainRegionAutomatonSurface as Region
import Ontology.BrainDNA.BrainRepresentationTransportLaws as Transport
import Ontology.BrainDNA.BrainThemeChemistryChannelTransport as ThemeTransport
import Ontology.BrainDNA.BrainChemistryCodecConsumer as Consumer
import Ontology.BrainDNA.BrainConnectorSemanticDepth as ConnectorDepth
import Ontology.BrainDNA.BrainAtomicChemistryHandoff as Handoff
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)
open import DASHI.Physics.Closure.AtomicChemistryRecoveryTheorem using
  (AtomicChemistryRecoveryTheorem)

------------------------------------------------------------------------
-- Bounded end-to-end semantic-depth surface over the currently consumed
-- brain -> DNA -> chemistry -> physics-facing connector chain.
--
-- This remains theorem-thin and non-claiming. It only packages exact
-- order/width/admissibility/recovery-boundary/cross-band/Hamiltonian
-- coherence already witnessed by the landed connector-chain owners.

record BrainConnectorEndToEndSemanticProfile (n : Nat) : Set where
  constructor mkBrainConnectorEndToEndSemanticProfile
  field
    order : ScanOrder
    width : Nat
    emittedAdmissibility : Bool
    recoveryBoundary : Nat
    crossBand : Nat
    hamiltonian : Nat

brainConnectorEndToEndSemanticProfile :
  ∀ {n} → BrainState n → Region.BrainRegion → BrainConnectorEndToEndSemanticProfile n
brainConnectorEndToEndSemanticProfile st r =
  mkBrainConnectorEndToEndSemanticProfile
    (ConnectorDepth.BrainConnectorSemanticDepthProfile.order
      (ConnectorDepth.brainConnectorSemanticDepthProfile st r))
    (Handoff.BrainAtomicChemistryHandoffProfile.width
      (Handoff.brainAtomicChemistryHandoffProfileOf st))
    (Consumer.BrainChemistryCodecConsumerProfile.emittedAdmissibility
      (Consumer.brainChemistryCodecConsumerProfile st))
    (ConnectorDepth.BrainConnectorSemanticDepthProfile.recoveryBoundary
      (ConnectorDepth.brainConnectorSemanticDepthProfile st r))
    (Handoff.BrainAtomicChemistryHandoffProfile.crossBand
      (Handoff.brainAtomicChemistryHandoffProfileOf st))
    (Handoff.BrainAtomicChemistryHandoffProfile.hamiltonian
      (Handoff.brainAtomicChemistryHandoffProfileOf st))

endToEndOrderMatchesTransport :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorEndToEndSemanticProfile.order
    (brainConnectorEndToEndSemanticProfile st r)
    ≡
  ConnectorDepth.BrainConnectorSemanticDepthProfile.order
    (ConnectorDepth.brainConnectorSemanticDepthProfile st r)
endToEndOrderMatchesTransport st r = refl

endToEndOrderLineMajor :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorEndToEndSemanticProfile.order
    (brainConnectorEndToEndSemanticProfile st r)
    ≡
  lineMajor
endToEndOrderLineMajor st r =
  Transport.transportOrderLineMajor st r

endToEndWidthMatchesTransport :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorEndToEndSemanticProfile.width
    (brainConnectorEndToEndSemanticProfile st r)
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.width
    (Handoff.brainAtomicChemistryHandoffProfileOf st)
endToEndWidthMatchesTransport st r = refl

endToEndWidthMatchesThemeTransport :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorEndToEndSemanticProfile.width
    (brainConnectorEndToEndSemanticProfile st r)
    ≡
  n
endToEndWidthMatchesThemeTransport st r =
  ThemeTransport.transportVisualWidthExact st r

endToEndAdmissibilityMatchesConsumer :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorEndToEndSemanticProfile.emittedAdmissibility
    (brainConnectorEndToEndSemanticProfile st r)
    ≡
  Consumer.BrainChemistryCodecConsumerProfile.emittedAdmissibility
    (Consumer.brainChemistryCodecConsumerProfile st)
endToEndAdmissibilityMatchesConsumer st r = refl

endToEndAdmissibilityMatchesTransport :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorEndToEndSemanticProfile.emittedAdmissibility
    (brainConnectorEndToEndSemanticProfile st r)
    ≡
  Consumer.BrainChemistryCodecConsumerProfile.emittedAdmissibility
    (Consumer.brainChemistryCodecConsumerProfile st)
endToEndAdmissibilityMatchesTransport st r =
  refl

endToEndRecoveryBoundaryExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorEndToEndSemanticProfile.recoveryBoundary
    (brainConnectorEndToEndSemanticProfile st r)
    ≡
  3
endToEndRecoveryBoundaryExact st r =
  ConnectorDepth.connectorSemanticDepthRecoveryBoundaryExact st r

endToEndRecoveryBoundaryMatchesTransport :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorEndToEndSemanticProfile.recoveryBoundary
    (brainConnectorEndToEndSemanticProfile st r)
    ≡
  Consumer.BrainChemistryCodecConsumerProfile.recoveryBoundary
    (Consumer.brainChemistryCodecConsumerProfile st)
endToEndRecoveryBoundaryMatchesTransport st r =
  Transport.transportRecoveryBoundaryMatchesConsumer st r

endToEndRecoveryBoundaryMatchesHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorEndToEndSemanticProfile.recoveryBoundary
    (brainConnectorEndToEndSemanticProfile st r)
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.recoveryBoundary
    (Handoff.brainAtomicChemistryHandoffProfileOf st)
endToEndRecoveryBoundaryMatchesHandoff st r =
  Transport.transportRecoveryBoundaryMatchesHandoff st r

endToEndCrossBandMatchesHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorEndToEndSemanticProfile.crossBand
    (brainConnectorEndToEndSemanticProfile st r)
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.crossBand
    (Handoff.brainAtomicChemistryHandoffProfileOf st)
endToEndCrossBandMatchesHandoff st r = refl

endToEndCrossBandMatchesConnectorDepth :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorEndToEndSemanticProfile.crossBand
    (brainConnectorEndToEndSemanticProfile st r)
    ≡
  ConnectorDepth.BrainConnectorSemanticDepthProfile.crossBand
    (ConnectorDepth.brainConnectorSemanticDepthProfile st r)
endToEndCrossBandMatchesConnectorDepth st r =
  ConnectorDepth.connectorSemanticDepthCrossBandMatchesHandoff st r

endToEndHamiltonianMatchesHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorEndToEndSemanticProfile.hamiltonian
    (brainConnectorEndToEndSemanticProfile st r)
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.hamiltonian
    (Handoff.brainAtomicChemistryHandoffProfileOf st)
endToEndHamiltonianMatchesHandoff st r = refl

endToEndHamiltonianMatchesConnectorDepth :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorEndToEndSemanticProfile.hamiltonian
    (brainConnectorEndToEndSemanticProfile st r)
    ≡
  ConnectorDepth.BrainConnectorSemanticDepthProfile.hamiltonian
    (ConnectorDepth.brainConnectorSemanticDepthProfile st r)
endToEndHamiltonianMatchesConnectorDepth st r =
  ConnectorDepth.connectorSemanticDepthHamiltonianMatchesHandoff st r

record BrainConnectorEndToEndSemanticDepthSurface : Setω where
  field
    representationTransport : Transport.BrainRepresentationTransportLawSurface
    themeChemistryTransport : ThemeTransport.BrainThemeChemistryChannelTransportSurface
    chemistryConsumer : Consumer.BrainChemistryCodecConsumerSurface
    connectorSemanticDepth : ConnectorDepth.BrainConnectorSemanticDepthSurface
    atomicHandoff : Handoff.BrainAtomicChemistryHandoffSurface
    physicsRecovery : AtomicChemistryRecoveryTheorem
    semanticProfile :
      ∀ {n} → BrainState n → Region.BrainRegion → BrainConnectorEndToEndSemanticProfile n

brainConnectorEndToEndSemanticDepthSurface :
  BrainConnectorEndToEndSemanticDepthSurface
brainConnectorEndToEndSemanticDepthSurface = record
  { representationTransport = Transport.brainRepresentationTransportLawSurface
  ; themeChemistryTransport = ThemeTransport.brainThemeChemistryChannelTransportSurface
  ; chemistryConsumer = Consumer.brainChemistryCodecConsumerSurface
  ; connectorSemanticDepth = ConnectorDepth.brainConnectorSemanticDepthSurface
  ; atomicHandoff = Handoff.brainAtomicChemistryHandoffSurface
  ; physicsRecovery = Handoff.BrainAtomicChemistryHandoffSurface.physicsRecovery
      Handoff.brainAtomicChemistryHandoffSurface
  ; semanticProfile = brainConnectorEndToEndSemanticProfile
  }
