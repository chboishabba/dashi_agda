module Ontology.BrainDNA.BrainConnectorEndToEndSemanticLaws where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
import Ontology.Brain.BrainRegionAutomatonSurface as Region
import Ontology.BrainDNA.BrainRepresentationSemanticDepth as Representation
import Ontology.BrainDNA.BrainThemeSemanticTransportLaws as Theme
import Ontology.BrainDNA.BrainConnectorEndToEndSemanticDepth as EndToEnd
import Ontology.BrainDNA.BrainAtomicChemistryHandoff as Handoff
import Ontology.BrainDNA.BrainChemistryCodecConsumer as Consumer
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)

------------------------------------------------------------------------
-- Bounded semantic-law surface over the current end-to-end connector chain.
--
-- This remains theorem-thin and non-claiming. It only packages exact
-- coherence witnesses already available from the representation semantic
-- depth, theme semantic transport, end-to-end semantic depth, chemistry
-- consumer, and atomic chemistry handoff owners.

record BrainConnectorEndToEndSemanticLawProfile (n : Nat) : Set where
  constructor mkBrainConnectorEndToEndSemanticLawProfile
  field
    order : ScanOrder
    width : Nat
    emittedAdmissibility : Bool
    recoveryBoundary : Nat
    thermoChecksum : Nat
    hamiltonian : Nat
    crossBand : Nat

brainConnectorEndToEndSemanticLawProfile :
  ∀ {n} → BrainState n → Region.BrainRegion → BrainConnectorEndToEndSemanticLawProfile n
brainConnectorEndToEndSemanticLawProfile st r =
  mkBrainConnectorEndToEndSemanticLawProfile
    (EndToEnd.BrainConnectorEndToEndSemanticProfile.order
      (EndToEnd.brainConnectorEndToEndSemanticProfile st r))
    (EndToEnd.BrainConnectorEndToEndSemanticProfile.width
      (EndToEnd.brainConnectorEndToEndSemanticProfile st r))
    (EndToEnd.BrainConnectorEndToEndSemanticProfile.emittedAdmissibility
      (EndToEnd.brainConnectorEndToEndSemanticProfile st r))
    (EndToEnd.BrainConnectorEndToEndSemanticProfile.recoveryBoundary
      (EndToEnd.brainConnectorEndToEndSemanticProfile st r))
    (Consumer.BrainChemistryCodecConsumerProfile.thermoChecksum
      (Consumer.brainChemistryCodecConsumerProfile st))
    (EndToEnd.BrainConnectorEndToEndSemanticProfile.hamiltonian
      (EndToEnd.brainConnectorEndToEndSemanticProfile st r))
    (EndToEnd.BrainConnectorEndToEndSemanticProfile.crossBand
      (EndToEnd.brainConnectorEndToEndSemanticProfile st r))

semanticLawOrderExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorEndToEndSemanticLawProfile.order
    (brainConnectorEndToEndSemanticLawProfile st r)
    ≡
  EndToEnd.BrainConnectorEndToEndSemanticProfile.order
    (EndToEnd.brainConnectorEndToEndSemanticProfile st r)
semanticLawOrderExact st r = refl

semanticLawOrderLineMajor :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorEndToEndSemanticLawProfile.order
    (brainConnectorEndToEndSemanticLawProfile st r)
    ≡
  lineMajor
semanticLawOrderLineMajor st r =
  EndToEnd.endToEndOrderLineMajor st r

semanticLawWidthExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorEndToEndSemanticLawProfile.width
    (brainConnectorEndToEndSemanticLawProfile st r)
    ≡
  n
semanticLawWidthExact st r =
  EndToEnd.endToEndWidthMatchesThemeTransport st r

semanticLawWidthMatchesRepresentation :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorEndToEndSemanticLawProfile.width
    (brainConnectorEndToEndSemanticLawProfile st r)
    ≡
  Representation.BrainRepresentationSemanticDepthProfile.width
    (Representation.brainRepresentationSemanticDepthProfile st r)
semanticLawWidthMatchesRepresentation st r =
  Representation.representationSemanticDepthWidthMatchesTransport st r

semanticLawEmittedAdmissibilityExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorEndToEndSemanticLawProfile.emittedAdmissibility
    (brainConnectorEndToEndSemanticLawProfile st r)
    ≡
  Consumer.BrainChemistryCodecConsumerProfile.emittedAdmissibility
    (Consumer.brainChemistryCodecConsumerProfile st)
semanticLawEmittedAdmissibilityExact st r = refl

semanticLawEmittedAdmissibilityMatchesRepresentation :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorEndToEndSemanticLawProfile.emittedAdmissibility
    (brainConnectorEndToEndSemanticLawProfile st r)
    ≡
  Representation.BrainRepresentationSemanticDepthProfile.emittedAdmissibility
    (Representation.brainRepresentationSemanticDepthProfile st r)
semanticLawEmittedAdmissibilityMatchesRepresentation st r =
  Representation.representationSemanticDepthEmittedAdmissibilityMatchesHandoffChain st r

semanticLawRecoveryBoundaryExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorEndToEndSemanticLawProfile.recoveryBoundary
    (brainConnectorEndToEndSemanticLawProfile st r)
    ≡
  3
semanticLawRecoveryBoundaryExact st r =
  EndToEnd.endToEndRecoveryBoundaryExact st r

semanticLawRecoveryBoundaryMatchesHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorEndToEndSemanticLawProfile.recoveryBoundary
    (brainConnectorEndToEndSemanticLawProfile st r)
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.recoveryBoundary
    (Handoff.brainAtomicChemistryHandoffProfileOf st)
semanticLawRecoveryBoundaryMatchesHandoff st r =
  EndToEnd.endToEndRecoveryBoundaryMatchesHandoff st r

semanticLawThermoMatchesConsumer :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorEndToEndSemanticLawProfile.thermoChecksum
    (brainConnectorEndToEndSemanticLawProfile st r)
    ≡
  Consumer.BrainChemistryCodecConsumerProfile.thermoChecksum
    (Consumer.brainChemistryCodecConsumerProfile st)
semanticLawThermoMatchesConsumer st r = refl

semanticLawHamiltonianMatchesHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorEndToEndSemanticLawProfile.hamiltonian
    (brainConnectorEndToEndSemanticLawProfile st r)
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.hamiltonian
    (Handoff.brainAtomicChemistryHandoffProfileOf st)
semanticLawHamiltonianMatchesHandoff st r =
  EndToEnd.endToEndHamiltonianMatchesHandoff st r

semanticLawCrossBandMatchesHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorEndToEndSemanticLawProfile.crossBand
    (brainConnectorEndToEndSemanticLawProfile st r)
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.crossBand
    (Handoff.brainAtomicChemistryHandoffProfileOf st)
semanticLawCrossBandMatchesHandoff st r =
  EndToEnd.endToEndCrossBandMatchesHandoff st r

semanticLawCrossBandMatchesTheme :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorEndToEndSemanticLawProfile.crossBand
    (brainConnectorEndToEndSemanticLawProfile st r)
    ≡
  Theme.BrainThemeSemanticTransportProfile.crossBand
    (Theme.brainThemeSemanticTransportProfile st r)
semanticLawCrossBandMatchesTheme st r =
  Theme.themeSemanticTransportCrossBandMatchesHandoff st r

record BrainConnectorEndToEndSemanticLawSurface : Setω where
  field
    representationSemanticDepth : Representation.BrainRepresentationSemanticDepthSurface
    themeSemanticTransport : Theme.BrainThemeSemanticTransportLawsSurface
    connectorSemanticDepth : EndToEnd.BrainConnectorEndToEndSemanticDepthSurface
    atomicHandoff : Handoff.BrainAtomicChemistryHandoffSurface
    chemistryConsumer : Consumer.BrainChemistryCodecConsumerSurface
    semanticLawProfile :
      ∀ {n} → BrainState n → Region.BrainRegion → BrainConnectorEndToEndSemanticLawProfile n

brainConnectorEndToEndSemanticLawSurface :
  BrainConnectorEndToEndSemanticLawSurface
brainConnectorEndToEndSemanticLawSurface = record
  { representationSemanticDepth = Representation.brainRepresentationSemanticDepthSurface
  ; themeSemanticTransport = Theme.brainThemeSemanticTransportLawsSurface
  ; connectorSemanticDepth = EndToEnd.brainConnectorEndToEndSemanticDepthSurface
  ; atomicHandoff = Handoff.brainAtomicChemistryHandoffSurface
  ; chemistryConsumer = Consumer.brainChemistryCodecConsumerSurface
  ; semanticLawProfile = brainConnectorEndToEndSemanticLawProfile
  }
