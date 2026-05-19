module Ontology.BrainDNA.BrainConnectorIntegratedConsumerLaws where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
import Ontology.Brain.BrainRegionAutomatonSurface as Region
import Ontology.BrainDNA.BrainConnectorIntegratedConsumerSemantics as Integrated
import Ontology.BrainDNA.BrainConnectorConsumerLaws as ConsumerLaws
import Ontology.BrainDNA.BrainConnectorEndToEndSemanticLaws as EndToEnd
import Ontology.BrainDNA.BrainChemistryCodecConsumer as Consumer
import Ontology.BrainDNA.BrainAtomicChemistryHandoff as Handoff
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)

------------------------------------------------------------------------
-- Bounded integrated whole-chain consumer/law surface beyond the current
-- integrated consumer semantics layer.
--
-- This remains theorem-thin and non-claiming. It only packages exact
-- coherence already witnessed by the integrated consumer semantics,
-- connector-consumer law, chemistry consumer, and physics-facing handoff
-- owners.

record BrainConnectorIntegratedConsumerLawProfile (n : Nat) : Set where
  constructor mkBrainConnectorIntegratedConsumerLawProfile
  field
    order : ScanOrder
    width : Nat
    emittedAdmissibility : Bool
    recoveryBoundary : Nat
    recoveredWidth : Nat
    thermoChecksum : Nat
    hamiltonian : Nat
    crossBand : Nat

brainConnectorIntegratedConsumerLawProfile :
  ∀ {n} → BrainState n → Region.BrainRegion → BrainConnectorIntegratedConsumerLawProfile n
brainConnectorIntegratedConsumerLawProfile st r =
  mkBrainConnectorIntegratedConsumerLawProfile
    (Integrated.BrainConnectorIntegratedConsumerProfile.order
      (Integrated.brainConnectorIntegratedConsumerProfile st r))
    (Integrated.BrainConnectorIntegratedConsumerProfile.width
      (Integrated.brainConnectorIntegratedConsumerProfile st r))
    (Integrated.BrainConnectorIntegratedConsumerProfile.emittedAdmissibility
      (Integrated.brainConnectorIntegratedConsumerProfile st r))
    (Integrated.BrainConnectorIntegratedConsumerProfile.recoveryBoundary
      (Integrated.brainConnectorIntegratedConsumerProfile st r))
    (Integrated.BrainConnectorIntegratedConsumerProfile.recoveredWidth
      (Integrated.brainConnectorIntegratedConsumerProfile st r))
    (Integrated.BrainConnectorIntegratedConsumerProfile.thermoChecksum
      (Integrated.brainConnectorIntegratedConsumerProfile st r))
    (Integrated.BrainConnectorIntegratedConsumerProfile.hamiltonian
      (Integrated.brainConnectorIntegratedConsumerProfile st r))
    (Integrated.BrainConnectorIntegratedConsumerProfile.crossBand
      (Integrated.brainConnectorIntegratedConsumerProfile st r))

integratedLawOrderExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorIntegratedConsumerLawProfile.order
    (brainConnectorIntegratedConsumerLawProfile st r)
    ≡
  Integrated.BrainConnectorIntegratedConsumerProfile.order
    (Integrated.brainConnectorIntegratedConsumerProfile st r)
integratedLawOrderExact st r = refl

integratedLawOrderLineMajor :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorIntegratedConsumerLawProfile.order
    (brainConnectorIntegratedConsumerLawProfile st r)
    ≡
  lineMajor
integratedLawOrderLineMajor st r =
  Integrated.integratedConsumerOrderLineMajor st r

integratedLawWidthExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorIntegratedConsumerLawProfile.width
    (brainConnectorIntegratedConsumerLawProfile st r)
    ≡
  n
integratedLawWidthExact st r =
  Integrated.integratedConsumerWidthExact st r

integratedLawWidthMatchesConnectorConsumer :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorIntegratedConsumerLawProfile.width
    (brainConnectorIntegratedConsumerLawProfile st r)
    ≡
  ConsumerLaws.BrainConnectorConsumerLawProfile.width
    (ConsumerLaws.brainConnectorConsumerLawProfile st r)
integratedLawWidthMatchesConnectorConsumer st r = refl

integratedLawWidthMatchesEndToEnd :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorIntegratedConsumerLawProfile.width
    (brainConnectorIntegratedConsumerLawProfile st r)
    ≡
  EndToEnd.BrainConnectorEndToEndSemanticLawProfile.width
    (EndToEnd.brainConnectorEndToEndSemanticLawProfile st r)
integratedLawWidthMatchesEndToEnd st r =
  Integrated.integratedConsumerWidthMatchesEndToEnd st r

integratedLawEmittedAdmissibilityExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorIntegratedConsumerLawProfile.emittedAdmissibility
    (brainConnectorIntegratedConsumerLawProfile st r)
    ≡
  Consumer.BrainChemistryCodecConsumerProfile.emittedAdmissibility
    (Consumer.brainChemistryCodecConsumerProfile st)
integratedLawEmittedAdmissibilityExact st r =
  Integrated.integratedConsumerEmittedAdmissibilityExact st r

integratedLawRecoveryBoundaryExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorIntegratedConsumerLawProfile.recoveryBoundary
    (brainConnectorIntegratedConsumerLawProfile st r)
    ≡
  3
integratedLawRecoveryBoundaryExact st r =
  Integrated.integratedConsumerRecoveryBoundaryExact st r

integratedLawRecoveryBoundaryMatchesHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorIntegratedConsumerLawProfile.recoveryBoundary
    (brainConnectorIntegratedConsumerLawProfile st r)
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.recoveryBoundary
    (Handoff.brainAtomicChemistryHandoffProfileOf st)
integratedLawRecoveryBoundaryMatchesHandoff st r =
  Integrated.integratedConsumerRecoveryBoundaryMatchesHandoff st r

integratedLawRecoveredWidthCanonical :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorIntegratedConsumerLawProfile.recoveredWidth
    (brainConnectorIntegratedConsumerLawProfile st r)
    ≡
  0
integratedLawRecoveredWidthCanonical st r =
  Integrated.integratedConsumerRecoveredWidthCanonical st r

integratedLawThermoMatchesConsumer :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorIntegratedConsumerLawProfile.thermoChecksum
    (brainConnectorIntegratedConsumerLawProfile st r)
    ≡
  Consumer.BrainChemistryCodecConsumerProfile.thermoChecksum
    (Consumer.brainChemistryCodecConsumerProfile st)
integratedLawThermoMatchesConsumer st r =
  Integrated.integratedConsumerThermoMatchesConsumer st r

integratedLawHamiltonianMatchesHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorIntegratedConsumerLawProfile.hamiltonian
    (brainConnectorIntegratedConsumerLawProfile st r)
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.hamiltonian
    (Handoff.brainAtomicChemistryHandoffProfileOf st)
integratedLawHamiltonianMatchesHandoff st r =
  Integrated.integratedConsumerHamiltonianMatchesHandoff st r

integratedLawCrossBandMatchesHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorIntegratedConsumerLawProfile.crossBand
    (brainConnectorIntegratedConsumerLawProfile st r)
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.crossBand
    (Handoff.brainAtomicChemistryHandoffProfileOf st)
integratedLawCrossBandMatchesHandoff st r =
  Integrated.integratedConsumerCrossBandMatchesHandoff st r

record BrainConnectorIntegratedConsumerLawSurface : Setω where
  field
    integratedConsumerSemantics :
      Integrated.BrainConnectorIntegratedConsumerSemanticsSurface
    connectorConsumerLaws : ConsumerLaws.BrainConnectorConsumerLawSurface
    connectorEndToEndLaws : EndToEnd.BrainConnectorEndToEndSemanticLawSurface
    chemistryConsumer : Consumer.BrainChemistryCodecConsumerSurface
    atomicHandoff : Handoff.BrainAtomicChemistryHandoffSurface
    integratedConsumerLawProfile :
      ∀ {n} → BrainState n → Region.BrainRegion → BrainConnectorIntegratedConsumerLawProfile n

brainConnectorIntegratedConsumerLawSurface :
  BrainConnectorIntegratedConsumerLawSurface
brainConnectorIntegratedConsumerLawSurface = record
  { integratedConsumerSemantics =
      Integrated.brainConnectorIntegratedConsumerSemanticsSurface
  ; connectorConsumerLaws = ConsumerLaws.brainConnectorConsumerLawSurface
  ; connectorEndToEndLaws = EndToEnd.brainConnectorEndToEndSemanticLawSurface
  ; chemistryConsumer = Consumer.brainChemistryCodecConsumerSurface
  ; atomicHandoff = Handoff.brainAtomicChemistryHandoffSurface
  ; integratedConsumerLawProfile = brainConnectorIntegratedConsumerLawProfile
  }
