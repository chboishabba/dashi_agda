module Ontology.BrainDNA.BrainConnectorIntegratedConsumerSemantics where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
import Ontology.Brain.BrainRegionAutomatonSurface as Region
import Ontology.BrainDNA.BrainConnectorConsumerLaws as ConsumerLaws
import Ontology.BrainDNA.BrainConnectorEndToEndSemanticLaws as EndToEnd
import Ontology.BrainDNA.BrainChemistryCodecConsumer as Consumer
import Ontology.BrainDNA.BrainAtomicChemistryHandoff as Handoff
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)

------------------------------------------------------------------------
-- Bounded integrated consumer semantics surface over the whole consumed
-- connector chain.
--
-- This remains theorem-thin and non-claiming. It only packages exact
-- coherence already witnessed by the current connector-consumer law,
-- end-to-end semantic law, chemistry codec consumer, and physics-facing
-- handoff owners.

record BrainConnectorIntegratedConsumerProfile (n : Nat) : Set where
  constructor mkBrainConnectorIntegratedConsumerProfile
  field
    order : ScanOrder
    width : Nat
    emittedAdmissibility : Bool
    recoveryBoundary : Nat
    recoveredWidth : Nat
    thermoChecksum : Nat
    hamiltonian : Nat
    crossBand : Nat

brainConnectorIntegratedConsumerProfile :
  ∀ {n} → BrainState n → Region.BrainRegion → BrainConnectorIntegratedConsumerProfile n
brainConnectorIntegratedConsumerProfile st r =
  mkBrainConnectorIntegratedConsumerProfile
    (ConsumerLaws.BrainConnectorConsumerLawProfile.order
      (ConsumerLaws.brainConnectorConsumerLawProfile st r))
    (ConsumerLaws.BrainConnectorConsumerLawProfile.width
      (ConsumerLaws.brainConnectorConsumerLawProfile st r))
    (ConsumerLaws.BrainConnectorConsumerLawProfile.emittedAdmissibility
      (ConsumerLaws.brainConnectorConsumerLawProfile st r))
    (ConsumerLaws.BrainConnectorConsumerLawProfile.recoveryBoundary
      (ConsumerLaws.brainConnectorConsumerLawProfile st r))
    (Consumer.BrainChemistryCodecConsumerProfile.recoveredWidth
      (Consumer.brainChemistryCodecConsumerProfile st))
    (ConsumerLaws.BrainConnectorConsumerLawProfile.thermoChecksum
      (ConsumerLaws.brainConnectorConsumerLawProfile st r))
    (ConsumerLaws.BrainConnectorConsumerLawProfile.hamiltonian
      (ConsumerLaws.brainConnectorConsumerLawProfile st r))
    (ConsumerLaws.BrainConnectorConsumerLawProfile.crossBand
      (ConsumerLaws.brainConnectorConsumerLawProfile st r))

integratedConsumerOrderExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorIntegratedConsumerProfile.order
    (brainConnectorIntegratedConsumerProfile st r)
    ≡
  ConsumerLaws.BrainConnectorConsumerLawProfile.order
    (ConsumerLaws.brainConnectorConsumerLawProfile st r)
integratedConsumerOrderExact st r = refl

integratedConsumerOrderLineMajor :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorIntegratedConsumerProfile.order
    (brainConnectorIntegratedConsumerProfile st r)
    ≡
  lineMajor
integratedConsumerOrderLineMajor st r =
  ConsumerLaws.consumerLawOrderLineMajor st r

integratedConsumerWidthExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorIntegratedConsumerProfile.width
    (brainConnectorIntegratedConsumerProfile st r)
    ≡
  n
integratedConsumerWidthExact st r =
  ConsumerLaws.consumerLawWidthExact st r

integratedConsumerWidthMatchesEndToEnd :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorIntegratedConsumerProfile.width
    (brainConnectorIntegratedConsumerProfile st r)
    ≡
  EndToEnd.BrainConnectorEndToEndSemanticLawProfile.width
    (EndToEnd.brainConnectorEndToEndSemanticLawProfile st r)
integratedConsumerWidthMatchesEndToEnd st r =
  ConsumerLaws.consumerLawWidthMatchesEndToEnd st r

integratedConsumerEmittedAdmissibilityExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorIntegratedConsumerProfile.emittedAdmissibility
    (brainConnectorIntegratedConsumerProfile st r)
    ≡
  Consumer.BrainChemistryCodecConsumerProfile.emittedAdmissibility
    (Consumer.brainChemistryCodecConsumerProfile st)
integratedConsumerEmittedAdmissibilityExact st r =
  ConsumerLaws.consumerLawEmittedAdmissibilityExact st r

integratedConsumerRecoveryBoundaryExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorIntegratedConsumerProfile.recoveryBoundary
    (brainConnectorIntegratedConsumerProfile st r)
    ≡
  3
integratedConsumerRecoveryBoundaryExact st r =
  ConsumerLaws.consumerLawRecoveryBoundaryExact st r

integratedConsumerRecoveryBoundaryMatchesHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorIntegratedConsumerProfile.recoveryBoundary
    (brainConnectorIntegratedConsumerProfile st r)
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.recoveryBoundary
    (Handoff.brainAtomicChemistryHandoffProfileOf st)
integratedConsumerRecoveryBoundaryMatchesHandoff st r =
  ConsumerLaws.consumerLawRecoveryBoundaryMatchesHandoff st r

integratedConsumerRecoveredWidthCanonical :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorIntegratedConsumerProfile.recoveredWidth
    (brainConnectorIntegratedConsumerProfile st r)
    ≡
  0
integratedConsumerRecoveredWidthCanonical st r =
  Consumer.consumerRecoveredWidthCanonical st

integratedConsumerThermoMatchesConsumer :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorIntegratedConsumerProfile.thermoChecksum
    (brainConnectorIntegratedConsumerProfile st r)
    ≡
  Consumer.BrainChemistryCodecConsumerProfile.thermoChecksum
    (Consumer.brainChemistryCodecConsumerProfile st)
integratedConsumerThermoMatchesConsumer st r =
  ConsumerLaws.consumerLawThermoMatchesConsumer st r

integratedConsumerHamiltonianMatchesHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorIntegratedConsumerProfile.hamiltonian
    (brainConnectorIntegratedConsumerProfile st r)
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.hamiltonian
    (Handoff.brainAtomicChemistryHandoffProfileOf st)
integratedConsumerHamiltonianMatchesHandoff st r =
  ConsumerLaws.consumerLawHamiltonianMatchesHandoff st r

integratedConsumerCrossBandMatchesHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorIntegratedConsumerProfile.crossBand
    (brainConnectorIntegratedConsumerProfile st r)
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.crossBand
    (Handoff.brainAtomicChemistryHandoffProfileOf st)
integratedConsumerCrossBandMatchesHandoff st r =
  ConsumerLaws.consumerLawCrossBandMatchesHandoff st r

record BrainConnectorIntegratedConsumerSemanticsSurface : Setω where
  field
    connectorConsumerLaws : ConsumerLaws.BrainConnectorConsumerLawSurface
    connectorEndToEndLaws : EndToEnd.BrainConnectorEndToEndSemanticLawSurface
    chemistryConsumer : Consumer.BrainChemistryCodecConsumerSurface
    atomicHandoff : Handoff.BrainAtomicChemistryHandoffSurface
    integratedConsumerProfile :
      ∀ {n} → BrainState n → Region.BrainRegion → BrainConnectorIntegratedConsumerProfile n

brainConnectorIntegratedConsumerSemanticsSurface :
  BrainConnectorIntegratedConsumerSemanticsSurface
brainConnectorIntegratedConsumerSemanticsSurface = record
  { connectorConsumerLaws = ConsumerLaws.brainConnectorConsumerLawSurface
  ; connectorEndToEndLaws = EndToEnd.brainConnectorEndToEndSemanticLawSurface
  ; chemistryConsumer = Consumer.brainChemistryCodecConsumerSurface
  ; atomicHandoff = Handoff.brainAtomicChemistryHandoffSurface
  ; integratedConsumerProfile = brainConnectorIntegratedConsumerProfile
  }
