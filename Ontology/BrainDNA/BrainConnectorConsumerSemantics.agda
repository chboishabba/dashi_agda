module Ontology.BrainDNA.BrainConnectorConsumerSemantics where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
import Ontology.Brain.BrainRegionAutomatonSurface as Region
import Ontology.BrainDNA.BrainRepresentationSemanticLaws as Representation
import Ontology.BrainDNA.BrainThemeEndToEndSemanticDepth as Theme
import Ontology.BrainDNA.BrainConnectorEndToEndSemanticLaws as Connector
import Ontology.BrainDNA.BrainChemistryCodecConsumer as Consumer
import Ontology.BrainDNA.BrainAtomicChemistryHandoff as Handoff
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)

------------------------------------------------------------------------
-- Bounded downstream consumer/semantic surface over the current
-- representation -> theme -> connector -> chemistry -> handoff chain.
--
-- This remains theorem-thin and non-claiming. It only packages exact
-- downstream coherence already witnessed by the landed semantic/law
-- surfaces and the current chemistry-facing consumer/handoff owners.

record BrainConnectorConsumerSemanticProfile (n : Nat) : Set where
  constructor mkBrainConnectorConsumerSemanticProfile
  field
    order : ScanOrder
    width : Nat
    emittedAdmissibility : Bool
    recoveryBoundary : Nat
    thermoChecksum : Nat
    hamiltonian : Nat
    crossBand : Nat

brainConnectorConsumerSemanticProfile :
  ∀ {n} → BrainState n → Region.BrainRegion → BrainConnectorConsumerSemanticProfile n
brainConnectorConsumerSemanticProfile st r =
  mkBrainConnectorConsumerSemanticProfile
    (Connector.BrainConnectorEndToEndSemanticLawProfile.order
      (Connector.brainConnectorEndToEndSemanticLawProfile st r))
    (Connector.BrainConnectorEndToEndSemanticLawProfile.width
      (Connector.brainConnectorEndToEndSemanticLawProfile st r))
    (Connector.BrainConnectorEndToEndSemanticLawProfile.emittedAdmissibility
      (Connector.brainConnectorEndToEndSemanticLawProfile st r))
    (Connector.BrainConnectorEndToEndSemanticLawProfile.recoveryBoundary
      (Connector.brainConnectorEndToEndSemanticLawProfile st r))
    (Connector.BrainConnectorEndToEndSemanticLawProfile.thermoChecksum
      (Connector.brainConnectorEndToEndSemanticLawProfile st r))
    (Connector.BrainConnectorEndToEndSemanticLawProfile.hamiltonian
      (Connector.brainConnectorEndToEndSemanticLawProfile st r))
    (Connector.BrainConnectorEndToEndSemanticLawProfile.crossBand
      (Connector.brainConnectorEndToEndSemanticLawProfile st r))

consumerSemanticOrderExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorConsumerSemanticProfile.order
    (brainConnectorConsumerSemanticProfile st r)
    ≡
  Connector.BrainConnectorEndToEndSemanticLawProfile.order
    (Connector.brainConnectorEndToEndSemanticLawProfile st r)
consumerSemanticOrderExact st r = refl

consumerSemanticOrderLineMajor :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorConsumerSemanticProfile.order
    (brainConnectorConsumerSemanticProfile st r)
    ≡
  lineMajor
consumerSemanticOrderLineMajor st r =
  Connector.semanticLawOrderLineMajor st r

consumerSemanticWidthExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorConsumerSemanticProfile.width
    (brainConnectorConsumerSemanticProfile st r)
    ≡
  n
consumerSemanticWidthExact st r =
  Connector.semanticLawWidthExact st r

consumerSemanticWidthMatchesTheme :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorConsumerSemanticProfile.width
    (brainConnectorConsumerSemanticProfile st r)
    ≡
  Theme.BrainThemeEndToEndSemanticProfile.width
    (Theme.brainThemeEndToEndSemanticProfile st r)
consumerSemanticWidthMatchesTheme st r = refl

consumerSemanticEmittedAdmissibilityExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorConsumerSemanticProfile.emittedAdmissibility
    (brainConnectorConsumerSemanticProfile st r)
    ≡
  Consumer.BrainChemistryCodecConsumerProfile.emittedAdmissibility
    (Consumer.brainChemistryCodecConsumerProfile st)
consumerSemanticEmittedAdmissibilityExact st r =
  Connector.semanticLawEmittedAdmissibilityExact st r

consumerSemanticEmittedAdmissibilityMatchesRepresentation :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorConsumerSemanticProfile.emittedAdmissibility
    (brainConnectorConsumerSemanticProfile st r)
    ≡
  Representation.BrainRepresentationSemanticLawProfile.emittedAdmissibility
    (Representation.brainRepresentationSemanticLawProfile st r)
consumerSemanticEmittedAdmissibilityMatchesRepresentation st r =
  Connector.semanticLawEmittedAdmissibilityMatchesRepresentation st r

consumerSemanticRecoveryBoundaryExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorConsumerSemanticProfile.recoveryBoundary
    (brainConnectorConsumerSemanticProfile st r)
    ≡
  3
consumerSemanticRecoveryBoundaryExact st r =
  Connector.semanticLawRecoveryBoundaryExact st r

consumerSemanticRecoveryBoundaryMatchesHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorConsumerSemanticProfile.recoveryBoundary
    (brainConnectorConsumerSemanticProfile st r)
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.recoveryBoundary
    (Handoff.brainAtomicChemistryHandoffProfileOf st)
consumerSemanticRecoveryBoundaryMatchesHandoff st r =
  Connector.semanticLawRecoveryBoundaryMatchesHandoff st r

consumerSemanticThermoMatchesConsumer :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorConsumerSemanticProfile.thermoChecksum
    (brainConnectorConsumerSemanticProfile st r)
    ≡
  Consumer.BrainChemistryCodecConsumerProfile.thermoChecksum
    (Consumer.brainChemistryCodecConsumerProfile st)
consumerSemanticThermoMatchesConsumer st r = refl

consumerSemanticHamiltonianMatchesHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorConsumerSemanticProfile.hamiltonian
    (brainConnectorConsumerSemanticProfile st r)
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.hamiltonian
    (Handoff.brainAtomicChemistryHandoffProfileOf st)
consumerSemanticHamiltonianMatchesHandoff st r =
  Connector.semanticLawHamiltonianMatchesHandoff st r

consumerSemanticCrossBandMatchesHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorConsumerSemanticProfile.crossBand
    (brainConnectorConsumerSemanticProfile st r)
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.crossBand
    (Handoff.brainAtomicChemistryHandoffProfileOf st)
consumerSemanticCrossBandMatchesHandoff st r =
  Connector.semanticLawCrossBandMatchesHandoff st r

record BrainConnectorConsumerSemanticsSurface : Setω where
  field
    representationSemanticLaws : Representation.BrainRepresentationSemanticLawSurface
    themeSemanticDepth : Theme.BrainThemeEndToEndSemanticDepthSurface
    connectorSemanticLaws : Connector.BrainConnectorEndToEndSemanticLawSurface
    chemistryConsumer : Consumer.BrainChemistryCodecConsumerSurface
    atomicHandoff : Handoff.BrainAtomicChemistryHandoffSurface
    consumerSemanticProfile :
      ∀ {n} → BrainState n → Region.BrainRegion → BrainConnectorConsumerSemanticProfile n

brainConnectorConsumerSemanticsSurface : BrainConnectorConsumerSemanticsSurface
brainConnectorConsumerSemanticsSurface = record
  { representationSemanticLaws = Representation.brainRepresentationSemanticLawSurface
  ; themeSemanticDepth = Theme.brainThemeEndToEndSemanticDepthSurface
  ; connectorSemanticLaws = Connector.brainConnectorEndToEndSemanticLawSurface
  ; chemistryConsumer = Consumer.brainChemistryCodecConsumerSurface
  ; atomicHandoff = Handoff.brainAtomicChemistryHandoffSurface
  ; consumerSemanticProfile = brainConnectorConsumerSemanticProfile
  }
