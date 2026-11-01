module Ontology.BrainDNA.BrainConnectorConsumerLaws where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
import Ontology.Brain.BrainRegionAutomatonSurface as Region
import Ontology.BrainDNA.BrainConnectorConsumerSemantics as Connector
import Ontology.BrainDNA.BrainConnectorEndToEndSemanticLaws as EndToEnd
import Ontology.BrainDNA.BrainRepresentationConsumerSemantics as Representation
import Ontology.BrainDNA.BrainThemeConsumerSemantics as Theme
import Ontology.BrainDNA.BrainChemistryCodecConsumer as Consumer
import Ontology.BrainDNA.BrainAtomicChemistryHandoff as Handoff
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)

------------------------------------------------------------------------
-- Bounded downstream consumer/law surface beyond the current connector
-- consumer semantics layer.
--
-- This remains theorem-thin and non-claiming. It only packages exact
-- coherence witnesses already present across the current representation,
-- theme transport, chemistry/channel consumer, and physics-facing handoff
-- surfaces.

record BrainConnectorConsumerLawProfile (n : Nat) : Set where
  constructor mkBrainConnectorConsumerLawProfile
  field
    order : ScanOrder
    width : Nat
    emittedAdmissibility : Bool
    recoveryBoundary : Nat
    thermoChecksum : Nat
    hamiltonian : Nat
    crossBand : Nat

brainConnectorConsumerLawProfile :
  ∀ {n} → BrainState n → Region.BrainRegion → BrainConnectorConsumerLawProfile n
brainConnectorConsumerLawProfile st r =
  mkBrainConnectorConsumerLawProfile
    (Connector.BrainConnectorConsumerSemanticProfile.order
      (Connector.brainConnectorConsumerSemanticProfile st r))
    (Connector.BrainConnectorConsumerSemanticProfile.width
      (Connector.brainConnectorConsumerSemanticProfile st r))
    (Connector.BrainConnectorConsumerSemanticProfile.emittedAdmissibility
      (Connector.brainConnectorConsumerSemanticProfile st r))
    (Connector.BrainConnectorConsumerSemanticProfile.recoveryBoundary
      (Connector.brainConnectorConsumerSemanticProfile st r))
    (Connector.BrainConnectorConsumerSemanticProfile.thermoChecksum
      (Connector.brainConnectorConsumerSemanticProfile st r))
    (Connector.BrainConnectorConsumerSemanticProfile.hamiltonian
      (Connector.brainConnectorConsumerSemanticProfile st r))
    (Connector.BrainConnectorConsumerSemanticProfile.crossBand
      (Connector.brainConnectorConsumerSemanticProfile st r))

consumerLawOrderExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorConsumerLawProfile.order
    (brainConnectorConsumerLawProfile st r)
    ≡
  Connector.BrainConnectorConsumerSemanticProfile.order
    (Connector.brainConnectorConsumerSemanticProfile st r)
consumerLawOrderExact st r = refl

consumerLawOrderLineMajor :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorConsumerLawProfile.order
    (brainConnectorConsumerLawProfile st r)
    ≡
  lineMajor
consumerLawOrderLineMajor st r =
  Connector.consumerSemanticOrderLineMajor st r

consumerLawWidthExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorConsumerLawProfile.width
    (brainConnectorConsumerLawProfile st r)
    ≡
  n
consumerLawWidthExact st r =
  Connector.consumerSemanticWidthExact st r

consumerLawWidthMatchesRepresentation :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorConsumerLawProfile.width
    (brainConnectorConsumerLawProfile st r)
    ≡
  Representation.BrainRepresentationConsumerProfile.width
    (Representation.brainRepresentationConsumerProfile st r)
consumerLawWidthMatchesRepresentation st r = refl

consumerLawWidthMatchesTheme :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorConsumerLawProfile.width
    (brainConnectorConsumerLawProfile st r)
    ≡
  Theme.BrainThemeConsumerSemanticProfile.width
    (Theme.brainThemeConsumerSemanticProfile st r)
consumerLawWidthMatchesTheme st r =
  Connector.consumerSemanticWidthMatchesTheme st r

consumerLawWidthMatchesEndToEnd :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorConsumerLawProfile.width
    (brainConnectorConsumerLawProfile st r)
    ≡
  EndToEnd.BrainConnectorEndToEndSemanticLawProfile.width
    (EndToEnd.brainConnectorEndToEndSemanticLawProfile st r)
consumerLawWidthMatchesEndToEnd st r = refl

consumerLawEmittedAdmissibilityExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorConsumerLawProfile.emittedAdmissibility
    (brainConnectorConsumerLawProfile st r)
    ≡
  Consumer.BrainChemistryCodecConsumerProfile.emittedAdmissibility
    (Consumer.brainChemistryCodecConsumerProfile st)
consumerLawEmittedAdmissibilityExact st r =
  Connector.consumerSemanticEmittedAdmissibilityExact st r

consumerLawEmittedAdmissibilityMatchesRepresentation :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorConsumerLawProfile.emittedAdmissibility
    (brainConnectorConsumerLawProfile st r)
    ≡
  Representation.BrainRepresentationConsumerProfile.emittedAdmissibility
    (Representation.brainRepresentationConsumerProfile st r)
consumerLawEmittedAdmissibilityMatchesRepresentation st r =
  Connector.consumerSemanticEmittedAdmissibilityMatchesRepresentation st r

consumerLawRecoveryBoundaryExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorConsumerLawProfile.recoveryBoundary
    (brainConnectorConsumerLawProfile st r)
    ≡
  3
consumerLawRecoveryBoundaryExact st r =
  Connector.consumerSemanticRecoveryBoundaryExact st r

consumerLawRecoveryBoundaryMatchesHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorConsumerLawProfile.recoveryBoundary
    (brainConnectorConsumerLawProfile st r)
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.recoveryBoundary
    (Handoff.brainAtomicChemistryHandoffProfileOf st)
consumerLawRecoveryBoundaryMatchesHandoff st r =
  Connector.consumerSemanticRecoveryBoundaryMatchesHandoff st r

consumerLawThermoMatchesConsumer :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorConsumerLawProfile.thermoChecksum
    (brainConnectorConsumerLawProfile st r)
    ≡
  Consumer.BrainChemistryCodecConsumerProfile.thermoChecksum
    (Consumer.brainChemistryCodecConsumerProfile st)
consumerLawThermoMatchesConsumer st r =
  Connector.consumerSemanticThermoMatchesConsumer st r

consumerLawHamiltonianMatchesHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorConsumerLawProfile.hamiltonian
    (brainConnectorConsumerLawProfile st r)
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.hamiltonian
    (Handoff.brainAtomicChemistryHandoffProfileOf st)
consumerLawHamiltonianMatchesHandoff st r =
  Connector.consumerSemanticHamiltonianMatchesHandoff st r

consumerLawCrossBandMatchesHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorConsumerLawProfile.crossBand
    (brainConnectorConsumerLawProfile st r)
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.crossBand
    (Handoff.brainAtomicChemistryHandoffProfileOf st)
consumerLawCrossBandMatchesHandoff st r =
  Connector.consumerSemanticCrossBandMatchesHandoff st r

record BrainConnectorConsumerLawSurface : Setω where
  field
    connectorConsumerSemantics : Connector.BrainConnectorConsumerSemanticsSurface
    connectorEndToEndLaws : EndToEnd.BrainConnectorEndToEndSemanticLawSurface
    representationConsumer : Representation.BrainRepresentationConsumerSemanticSurface
    themeConsumer : Theme.BrainThemeConsumerSemanticsSurface
    chemistryConsumer : Consumer.BrainChemistryCodecConsumerSurface
    atomicHandoff : Handoff.BrainAtomicChemistryHandoffSurface
    consumerLawProfile :
      ∀ {n} → BrainState n → Region.BrainRegion → BrainConnectorConsumerLawProfile n

brainConnectorConsumerLawSurface : BrainConnectorConsumerLawSurface
brainConnectorConsumerLawSurface = record
  { connectorConsumerSemantics = Connector.brainConnectorConsumerSemanticsSurface
  ; connectorEndToEndLaws = EndToEnd.brainConnectorEndToEndSemanticLawSurface
  ; representationConsumer = Representation.brainRepresentationConsumerSemanticSurface
  ; themeConsumer = Theme.brainThemeConsumerSemanticsSurface
  ; chemistryConsumer = Consumer.brainChemistryCodecConsumerSurface
  ; atomicHandoff = Handoff.brainAtomicChemistryHandoffSurface
  ; consumerLawProfile = brainConnectorConsumerLawProfile
  }
