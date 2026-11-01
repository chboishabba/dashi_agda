module Ontology.BrainDNA.BrainThemeChemistryChannelTransport where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
import Ontology.Brain.BrainRegionAutomatonSurface as Region
import Ontology.Brain.BrainVisualFormConstantSurface as Visual
import Ontology.Brain.BrainLearningEigenbasisSurface as Learn
import Ontology.Brain.BrainInvariantSemanticLaws as Semantic
import Ontology.Brain.BrainMorphospaceGapJunctionSurface as Morph
import Ontology.BrainDNA.BrainThemeConnectorSurface as Theme
import Ontology.BrainDNA.BrainChemistryCodecConsumer as Consumer
import Ontology.BrainDNA.BrainAtomicChemistryHandoff as Handoff
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)

------------------------------------------------------------------------
-- Bounded transport surface from the four localized brain themes into the
-- current channel/chemistry/handoff boundary.
--
-- This remains theorem-thin and non-claiming: it packages exact transport
-- witnesses only. It does not claim a realistic neuroscience decoding map,
-- biological recovery, or full theme semantics through chemistry.

record BrainThemeChemistryChannelTransportProfile (n : Nat) : Set where
  constructor mkBrainThemeChemistryChannelTransportProfile
  field
    lens : Region.RegionLens
    motif : Region.RegionMotif
    visualClass : Visual.BrainVisualFormConstant
    learningPhase : Learn.BrainRepresentationPhase
    morphSemantic : Semantic.BrainInvariantSemantic
    order : ScanOrder
    recoveryBoundary : Nat
    crossBand : Nat
    hamiltonian : Nat

brainThemeChemistryChannelTransportProfile :
  ∀ {n} → BrainState n → Region.BrainRegion → BrainThemeChemistryChannelTransportProfile n
brainThemeChemistryChannelTransportProfile st r =
  mkBrainThemeChemistryChannelTransportProfile
    (Region.RegionCorrespondence.lens
      (Theme.BrainThemeProfile.regionCorrespondence (Theme.themeProfileOf st r)))
    (Region.RegionCorrespondence.motif
      (Theme.BrainThemeProfile.regionCorrespondence (Theme.themeProfileOf st r)))
    (Theme.BrainThemeProfile.visualClass (Theme.themeProfileOf st r))
    (Learn.BrainLearningEigenbasisProfile.phase
      (Theme.BrainThemeProfile.learningProfile (Theme.themeProfileOf st r)))
    (Morph.BrainMorphospacePoint.semantic
      (Theme.BrainThemeProfile.morphospacePoint (Theme.themeProfileOf st r)))
    (Handoff.BrainAtomicChemistryHandoffProfile.order
      (Handoff.brainAtomicChemistryHandoffProfileOf st))
    (Consumer.BrainChemistryCodecConsumerProfile.recoveryBoundary
      (Consumer.brainChemistryCodecConsumerProfile st))
    (Handoff.BrainAtomicChemistryHandoffProfile.crossBand
      (Handoff.brainAtomicChemistryHandoffProfileOf st))
    (Handoff.BrainAtomicChemistryHandoffProfile.hamiltonian
      (Handoff.brainAtomicChemistryHandoffProfileOf st))

transportLensExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeChemistryChannelTransportProfile.lens
    (brainThemeChemistryChannelTransportProfile st r)
    ≡
  Region.lensOf r
transportLensExact st r = Theme.themeRegionLensExact st r

transportMotifExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeChemistryChannelTransportProfile.motif
    (brainThemeChemistryChannelTransportProfile st r)
    ≡
  Region.motifOf r
transportMotifExact st r = Theme.themeRegionMotifExact st r

transportVisualWidthExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  Visual.BrainLogPolarGeometry.radialRing
    (Theme.BrainThemeProfile.visualGeometry (Theme.themeProfileOf st r))
    ≡
  n
transportVisualWidthExact st r = Theme.themeVisualWidthExact st r

transportLearningWidthExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  Learn.BrainLearningEigenbasisProfile.width
    (Theme.BrainThemeProfile.learningProfile (Theme.themeProfileOf st r))
    ≡
  n
transportLearningWidthExact st r = Theme.themeLearningWidthExact st r

transportMorphWidthExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  Morph.BrainMorphospacePoint.width
    (Theme.BrainThemeProfile.morphospacePoint (Theme.themeProfileOf st r))
    ≡
  n
transportMorphWidthExact st r = Theme.themeMorphospaceWidthExact st r

transportOrderLineMajor :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeChemistryChannelTransportProfile.order
    (brainThemeChemistryChannelTransportProfile st r)
    ≡
  lineMajor
transportOrderLineMajor st r = Handoff.handoffOrderLineMajor st

transportRecoveryBoundaryExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeChemistryChannelTransportProfile.recoveryBoundary
    (brainThemeChemistryChannelTransportProfile st r)
    ≡
  3
transportRecoveryBoundaryExact st r =
  Consumer.consumerRecoveryBoundaryExact st

transportCrossBandMatchesHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeChemistryChannelTransportProfile.crossBand
    (brainThemeChemistryChannelTransportProfile st r)
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.crossBand
    (Handoff.brainAtomicChemistryHandoffProfileOf st)
transportCrossBandMatchesHandoff st r = refl

transportHamiltonianMatchesHandoff :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeChemistryChannelTransportProfile.hamiltonian
    (brainThemeChemistryChannelTransportProfile st r)
    ≡
  Handoff.BrainAtomicChemistryHandoffProfile.hamiltonian
    (Handoff.brainAtomicChemistryHandoffProfileOf st)
transportHamiltonianMatchesHandoff st r = refl

record BrainThemeChemistryChannelTransportSurface : Setω where
  field
    regionSurface : Region.BrainRegionAutomatonSurface
    visualSurface : Visual.BrainVisualFormConstantSurface
    learningSurface : Learn.BrainLearningEigenbasisSurface
    morphospaceSurface : Morph.BrainMorphospaceGapJunctionSurface
    themeConnector : Theme.BrainThemeConnectorSurface
    chemistryConsumer : Consumer.BrainChemistryCodecConsumerSurface
    chemistryHandoff : Handoff.BrainAtomicChemistryHandoffSurface
    transportProfile :
      ∀ {n} → BrainState n → Region.BrainRegion → BrainThemeChemistryChannelTransportProfile n

brainThemeChemistryChannelTransportSurface :
  BrainThemeChemistryChannelTransportSurface
brainThemeChemistryChannelTransportSurface = record
  { regionSurface = Region.brainRegionAutomatonSurface
  ; visualSurface = Visual.brainVisualFormConstantSurface
  ; learningSurface = Learn.brainLearningEigenbasisSurface
  ; morphospaceSurface = Morph.brainMorphospaceGapJunctionSurface
  ; themeConnector = Theme.brainThemeConnectorSurface
  ; chemistryConsumer = Consumer.brainChemistryCodecConsumerSurface
  ; chemistryHandoff = Handoff.brainAtomicChemistryHandoffSurface
  ; transportProfile = brainThemeChemistryChannelTransportProfile
  }
