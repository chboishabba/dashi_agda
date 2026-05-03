module Ontology.BrainDNA.BrainConnectorSemanticDepth where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
import Ontology.Brain.BrainRegionAutomatonSurface as Region
import Ontology.Brain.BrainVisualFormConstantSurface as Visual
import Ontology.BrainDNA.BrainThemeConnectorSurface as Theme
import Ontology.BrainDNA.BrainChemistryCodecConsumer as Consumer
import Ontology.BrainDNA.BrainAtomicChemistryHandoff as Handoff
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)

------------------------------------------------------------------------
-- Bounded semantic-depth surface over the currently consumed connector
-- chain. This stays theorem-thin and non-claiming: it only packages exact
-- transport/coherence facts already owned by the theme, consumer, and
-- chemistry handoff surfaces.

record BrainConnectorSemanticDepthProfile (n : Nat) : Set where
  constructor mkBrainConnectorSemanticDepthProfile
  field
    semanticDepth : Nat
    order : ScanOrder
    visualClass : Visual.BrainVisualFormConstant
    recoveryBoundary : Nat
    crossBand : Nat
    hamiltonian : Nat

brainConnectorSemanticDepthProfile :
  ∀ {n} → BrainState n → Region.BrainRegion → BrainConnectorSemanticDepthProfile n
brainConnectorSemanticDepthProfile st r =
  mkBrainConnectorSemanticDepthProfile
    (Consumer.BrainChemistryCodecConsumerProfile.invariantDepth
      (Consumer.brainChemistryCodecConsumerProfile st))
    (Handoff.BrainAtomicChemistryHandoffProfile.order
      (Handoff.brainAtomicChemistryHandoffProfileOf st))
    (Theme.BrainThemeProfile.visualClass
      (Theme.themeProfileOf st r))
    (Consumer.BrainChemistryCodecConsumerProfile.recoveryBoundary
      (Consumer.brainChemistryCodecConsumerProfile st))
    (Handoff.BrainAtomicChemistryHandoffProfile.crossBand
      (Handoff.brainAtomicChemistryHandoffProfileOf st))
    (Handoff.BrainAtomicChemistryHandoffProfile.hamiltonian
      (Handoff.brainAtomicChemistryHandoffProfileOf st))

connectorSemanticDepthOrderLineMajor :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorSemanticDepthProfile.order
    (brainConnectorSemanticDepthProfile st r)
    ≡
  lineMajor
connectorSemanticDepthOrderLineMajor st r =
  Handoff.handoffOrderLineMajor st

connectorSemanticDepthRecoveryBoundaryExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorSemanticDepthProfile.recoveryBoundary
    (brainConnectorSemanticDepthProfile st r)
    ≡
  3
connectorSemanticDepthRecoveryBoundaryExact st r =
  Consumer.consumerRecoveryBoundaryExact st

connectorSemanticDepthRecoveryBoundaryMatchesHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorSemanticDepthProfile.recoveryBoundary
    (brainConnectorSemanticDepthProfile st r)
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.recoveryBoundary
    (Handoff.brainAtomicChemistryHandoffProfileOf st)
connectorSemanticDepthRecoveryBoundaryMatchesHandoff st r = refl

connectorSemanticDepthCrossBandMatchesHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorSemanticDepthProfile.crossBand
    (brainConnectorSemanticDepthProfile st r)
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.crossBand
    (Handoff.brainAtomicChemistryHandoffProfileOf st)
connectorSemanticDepthCrossBandMatchesHandoff st r = refl

connectorSemanticDepthHamiltonianMatchesHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainConnectorSemanticDepthProfile.hamiltonian
    (brainConnectorSemanticDepthProfile st r)
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.hamiltonian
    (Handoff.brainAtomicChemistryHandoffProfileOf st)
connectorSemanticDepthHamiltonianMatchesHandoff st r = refl

connectorSemanticDepthVisualWidthExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  Visual.BrainLogPolarGeometry.radialRing
    (Theme.BrainThemeProfile.visualGeometry
      (Theme.themeProfileOf st r))
    ≡
  n
connectorSemanticDepthVisualWidthExact st r =
  Theme.themeVisualWidthExact st r

record BrainConnectorSemanticDepthSurface : Setω where
  field
    themeConnector : Theme.BrainThemeConnectorSurface
    chemistryConsumer : Consumer.BrainChemistryCodecConsumerSurface
    chemistryHandoff : Handoff.BrainAtomicChemistryHandoffSurface
    semanticDepthProfile :
      ∀ {n} → BrainState n → Region.BrainRegion → BrainConnectorSemanticDepthProfile n

brainConnectorSemanticDepthSurface : BrainConnectorSemanticDepthSurface
brainConnectorSemanticDepthSurface = record
  { themeConnector = Theme.brainThemeConnectorSurface
  ; chemistryConsumer = Consumer.brainChemistryCodecConsumerSurface
  ; chemistryHandoff = Handoff.brainAtomicChemistryHandoffSurface
  ; semanticDepthProfile = brainConnectorSemanticDepthProfile
  }
