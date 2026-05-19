module Ontology.BrainDNA.BrainThemeSemanticTransportLaws where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
import Ontology.Brain.BrainRegionAutomatonSurface as Region
import Ontology.Brain.BrainVisualFormConstantSurface as Visual
import Ontology.Brain.BrainLearningEigenbasisSurface as Learn
import Ontology.Brain.BrainInvariantSemanticLaws as Semantic
import Ontology.Brain.BrainMorphospaceGapJunctionSurface as Morph
import Ontology.BrainDNA.BrainThemeChemistryChannelTransport as Transport
import Ontology.BrainDNA.BrainChemistryCodecConsumer as Consumer
import Ontology.BrainDNA.BrainAtomicChemistryHandoff as Handoff
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)

------------------------------------------------------------------------
-- Bounded semantic-law deepening over the current theme transport lane.
--
-- This remains theorem-thin and non-claiming: it only exposes exact
-- alignment witnesses from the localized theme profiles into the current
-- chemistry/channel/handoff boundary.

record BrainThemeSemanticTransportProfile (n : Nat) : Set where
  constructor mkBrainThemeSemanticTransportProfile
  field
    lens : Region.RegionLens
    motif : Region.RegionMotif
    visualClass : Visual.BrainVisualFormConstant
    learningPhase : Learn.BrainRepresentationPhase
    morphSemantic : Semantic.BrainInvariantSemantic
    order : ScanOrder
    recoveryBoundary : Nat
    thermoChecksum : Nat
    hamiltonianChecksum : Nat
    crossBand : Nat

brainThemeSemanticTransportProfile :
  ∀ {n} → BrainState n → Region.BrainRegion → BrainThemeSemanticTransportProfile n
brainThemeSemanticTransportProfile st r =
  mkBrainThemeSemanticTransportProfile
    (Transport.BrainThemeChemistryChannelTransportProfile.lens
      (Transport.brainThemeChemistryChannelTransportProfile st r))
    (Transport.BrainThemeChemistryChannelTransportProfile.motif
      (Transport.brainThemeChemistryChannelTransportProfile st r))
    (Transport.BrainThemeChemistryChannelTransportProfile.visualClass
      (Transport.brainThemeChemistryChannelTransportProfile st r))
    (Transport.BrainThemeChemistryChannelTransportProfile.learningPhase
      (Transport.brainThemeChemistryChannelTransportProfile st r))
    (Transport.BrainThemeChemistryChannelTransportProfile.morphSemantic
      (Transport.brainThemeChemistryChannelTransportProfile st r))
    (Transport.BrainThemeChemistryChannelTransportProfile.order
      (Transport.brainThemeChemistryChannelTransportProfile st r))
    (Transport.BrainThemeChemistryChannelTransportProfile.recoveryBoundary
      (Transport.brainThemeChemistryChannelTransportProfile st r))
    (Consumer.BrainChemistryCodecConsumerProfile.thermoChecksum
      (Consumer.brainChemistryCodecConsumerProfile st))
    (Transport.BrainThemeChemistryChannelTransportProfile.hamiltonian
      (Transport.brainThemeChemistryChannelTransportProfile st r))
    (Transport.BrainThemeChemistryChannelTransportProfile.crossBand
      (Transport.brainThemeChemistryChannelTransportProfile st r))

themeSemanticTransportLensExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeSemanticTransportProfile.lens
    (brainThemeSemanticTransportProfile st r)
    ≡
  Region.lensOf r
themeSemanticTransportLensExact st r =
  Transport.transportLensExact st r

themeSemanticTransportMotifExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeSemanticTransportProfile.motif
    (brainThemeSemanticTransportProfile st r)
    ≡
  Region.motifOf r
themeSemanticTransportMotifExact st r =
  Transport.transportMotifExact st r

themeSemanticTransportVisualWidthExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  Visual.BrainLogPolarGeometry.radialRing
    (Visual.geometryOfState st)
    ≡
  n
themeSemanticTransportVisualWidthExact st r =
  Transport.transportVisualWidthExact st r

themeSemanticTransportLearningPhaseWidthExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  Learn.BrainLearningEigenbasisProfile.width
    (Learn.profileOfState st)
    ≡
  n
themeSemanticTransportLearningPhaseWidthExact st r =
  Transport.transportLearningWidthExact st r

themeSemanticTransportMorphSemanticExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeSemanticTransportProfile.morphSemantic
    (brainThemeSemanticTransportProfile st r)
    ≡
  Morph.BrainMorphospacePoint.semantic (Morph.morphospaceOfState st)
themeSemanticTransportMorphSemanticExact st r = refl

themeSemanticTransportOrderLineMajor :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeSemanticTransportProfile.order
    (brainThemeSemanticTransportProfile st r)
    ≡
  lineMajor
themeSemanticTransportOrderLineMajor st r =
  Transport.transportOrderLineMajor st r

themeSemanticTransportRecoveryBoundaryExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeSemanticTransportProfile.recoveryBoundary
    (brainThemeSemanticTransportProfile st r)
    ≡
  3
themeSemanticTransportRecoveryBoundaryExact st r =
  Transport.transportRecoveryBoundaryExact st r

themeSemanticTransportThermoMatchesConsumer :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeSemanticTransportProfile.thermoChecksum
    (brainThemeSemanticTransportProfile st r)
    ≡
  Consumer.BrainChemistryCodecConsumerProfile.thermoChecksum
    (Consumer.brainChemistryCodecConsumerProfile st)
themeSemanticTransportThermoMatchesConsumer st r = refl

themeSemanticTransportHamiltonianMatchesHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeSemanticTransportProfile.hamiltonianChecksum
    (brainThemeSemanticTransportProfile st r)
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.hamiltonian
    (Handoff.brainAtomicChemistryHandoffProfileOf st)
themeSemanticTransportHamiltonianMatchesHandoff st r =
  Transport.transportHamiltonianMatchesHandoff st r

themeSemanticTransportCrossBandMatchesHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeSemanticTransportProfile.crossBand
    (brainThemeSemanticTransportProfile st r)
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.crossBand
    (Handoff.brainAtomicChemistryHandoffProfileOf st)
themeSemanticTransportCrossBandMatchesHandoff st r =
  Transport.transportCrossBandMatchesHandoff st r

record BrainThemeSemanticTransportLawsSurface : Setω where
  field
    transportSurface : Transport.BrainThemeChemistryChannelTransportSurface
    chemistryConsumer : Consumer.BrainChemistryCodecConsumerSurface
    chemistryHandoff : Handoff.BrainAtomicChemistryHandoffSurface
    semanticProfile :
      ∀ {n} → BrainState n → Region.BrainRegion → BrainThemeSemanticTransportProfile n

brainThemeSemanticTransportLawsSurface :
  BrainThemeSemanticTransportLawsSurface
brainThemeSemanticTransportLawsSurface = record
  { transportSurface = Transport.brainThemeChemistryChannelTransportSurface
  ; chemistryConsumer = Consumer.brainChemistryCodecConsumerSurface
  ; chemistryHandoff = Handoff.brainAtomicChemistryHandoffSurface
  ; semanticProfile = brainThemeSemanticTransportProfile
  }
