module Ontology.BrainDNA.BrainThemeConsumerSemantics where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
import Ontology.Brain.BrainRegionAutomatonSurface as Region
import Ontology.Brain.BrainVisualFormConstantSurface as Visual
import Ontology.Brain.BrainLearningEigenbasisSurface as Learn
import Ontology.Brain.BrainInvariantSemanticLaws as Semantic
import Ontology.Brain.BrainMorphospaceGapJunctionSurface as Morph
import Ontology.BrainDNA.BrainThemeChemistryChannelTransport as ThemeTransport
import Ontology.BrainDNA.BrainThemeSemanticTransportLaws as ThemeLaws
import Ontology.BrainDNA.BrainThemeEndToEndSemanticDepth as ThemeEnd
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)

------------------------------------------------------------------------
-- Bounded downstream consumer/semantic surface for blocker 2.
--
-- This remains theorem-thin and non-claiming: it packages exact alignment
-- from the localized theme profiles into the already-landed downstream
-- chemistry/channel/handoff consumer boundaries.

record BrainThemeConsumerSemanticProfile (n : Nat) : Set where
  constructor mkBrainThemeConsumerSemanticProfile
  field
    lens : Region.RegionLens
    motif : Region.RegionMotif
    visualClass : Visual.BrainVisualFormConstant
    learningPhase : Learn.BrainRepresentationPhase
    morphSemantic : Semantic.BrainInvariantSemantic
    order : ScanOrder
    width : Nat
    emittedAdmissibility : Bool
    recoveryBoundary : Nat
    thermoChecksum : Nat
    hamiltonianChecksum : Nat
    crossBand : Nat

brainThemeConsumerSemanticProfile :
  ∀ {n} → BrainState n → Region.BrainRegion → BrainThemeConsumerSemanticProfile n
brainThemeConsumerSemanticProfile st r =
  mkBrainThemeConsumerSemanticProfile
    (ThemeEnd.BrainThemeEndToEndSemanticProfile.lens
      (ThemeEnd.brainThemeEndToEndSemanticProfile st r))
    (ThemeEnd.BrainThemeEndToEndSemanticProfile.motif
      (ThemeEnd.brainThemeEndToEndSemanticProfile st r))
    (ThemeEnd.BrainThemeEndToEndSemanticProfile.visualClass
      (ThemeEnd.brainThemeEndToEndSemanticProfile st r))
    (ThemeEnd.BrainThemeEndToEndSemanticProfile.learningPhase
      (ThemeEnd.brainThemeEndToEndSemanticProfile st r))
    (ThemeEnd.BrainThemeEndToEndSemanticProfile.morphSemantic
      (ThemeEnd.brainThemeEndToEndSemanticProfile st r))
    (ThemeEnd.BrainThemeEndToEndSemanticProfile.order
      (ThemeEnd.brainThemeEndToEndSemanticProfile st r))
    (ThemeEnd.BrainThemeEndToEndSemanticProfile.width
      (ThemeEnd.brainThemeEndToEndSemanticProfile st r))
    (ThemeEnd.BrainThemeEndToEndSemanticProfile.emittedAdmissibility
      (ThemeEnd.brainThemeEndToEndSemanticProfile st r))
    (ThemeEnd.BrainThemeEndToEndSemanticProfile.recoveryBoundary
      (ThemeEnd.brainThemeEndToEndSemanticProfile st r))
    (ThemeEnd.BrainThemeEndToEndSemanticProfile.thermoChecksum
      (ThemeEnd.brainThemeEndToEndSemanticProfile st r))
    (ThemeEnd.BrainThemeEndToEndSemanticProfile.hamiltonianChecksum
      (ThemeEnd.brainThemeEndToEndSemanticProfile st r))
    (ThemeEnd.BrainThemeEndToEndSemanticProfile.crossBand
      (ThemeEnd.brainThemeEndToEndSemanticProfile st r))

consumerLensExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeConsumerSemanticProfile.lens
    (brainThemeConsumerSemanticProfile st r)
    ≡
  Region.lensOf r
consumerLensExact st r =
  ThemeEnd.themeEndToEndLensExact st r

consumerMotifExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeConsumerSemanticProfile.motif
    (brainThemeConsumerSemanticProfile st r)
    ≡
  Region.motifOf r
consumerMotifExact st r =
  ThemeEnd.themeEndToEndMotifExact st r

consumerVisualClassMatchesTheme :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeConsumerSemanticProfile.visualClass
    (brainThemeConsumerSemanticProfile st r)
    ≡
  ThemeLaws.BrainThemeSemanticTransportProfile.visualClass
    (ThemeLaws.brainThemeSemanticTransportProfile st r)
consumerVisualClassMatchesTheme st r = refl

consumerLearningPhaseMatchesTheme :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeConsumerSemanticProfile.learningPhase
    (brainThemeConsumerSemanticProfile st r)
    ≡
  ThemeLaws.BrainThemeSemanticTransportProfile.learningPhase
    (ThemeLaws.brainThemeSemanticTransportProfile st r)
consumerLearningPhaseMatchesTheme st r = refl

consumerMorphSemanticExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeConsumerSemanticProfile.morphSemantic
    (brainThemeConsumerSemanticProfile st r)
    ≡
  Morph.BrainMorphospacePoint.semantic (Morph.morphospaceOfState st)
consumerMorphSemanticExact st r =
  ThemeEnd.themeEndToEndMorphSemanticExact st r

consumerOrderLineMajor :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeConsumerSemanticProfile.order
    (brainThemeConsumerSemanticProfile st r)
    ≡
  lineMajor
consumerOrderLineMajor st r =
  ThemeEnd.themeEndToEndOrderLineMajor st r

consumerWidthExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeConsumerSemanticProfile.width
    (brainThemeConsumerSemanticProfile st r)
    ≡
  n
consumerWidthExact st r =
  ThemeEnd.themeEndToEndVisualWidthExact st r

consumerRecoveryBoundaryExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeConsumerSemanticProfile.recoveryBoundary
    (brainThemeConsumerSemanticProfile st r)
    ≡
  3
consumerRecoveryBoundaryExact st r =
  ThemeEnd.themeEndToEndRecoveryBoundaryExact st r

consumerThermoChecksumMatchesTheme :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeConsumerSemanticProfile.thermoChecksum
    (brainThemeConsumerSemanticProfile st r)
    ≡
  ThemeLaws.BrainThemeSemanticTransportProfile.thermoChecksum
    (ThemeLaws.brainThemeSemanticTransportProfile st r)
consumerThermoChecksumMatchesTheme st r =
  ThemeEnd.themeEndToEndThermoMatchesThemeTransport st r

consumerHamiltonianMatchesTheme :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeConsumerSemanticProfile.hamiltonianChecksum
    (brainThemeConsumerSemanticProfile st r)
    ≡
  ThemeLaws.BrainThemeSemanticTransportProfile.hamiltonianChecksum
    (ThemeLaws.brainThemeSemanticTransportProfile st r)
consumerHamiltonianMatchesTheme st r =
  ThemeEnd.themeEndToEndHamiltonianMatchesThemeTransport st r

consumerCrossBandMatchesTheme :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeConsumerSemanticProfile.crossBand
    (brainThemeConsumerSemanticProfile st r)
    ≡
  ThemeLaws.BrainThemeSemanticTransportProfile.crossBand
    (ThemeLaws.brainThemeSemanticTransportProfile st r)
consumerCrossBandMatchesTheme st r =
  ThemeEnd.themeEndToEndCrossBandMatchesThemeTransport st r

record BrainThemeConsumerSemanticsSurface : Setω where
  field
    themeTransport : ThemeTransport.BrainThemeChemistryChannelTransportSurface
    themeSemanticTransport : ThemeLaws.BrainThemeSemanticTransportLawsSurface
    themeEndToEnd : ThemeEnd.BrainThemeEndToEndSemanticDepthSurface
    consumerProfile :
      ∀ {n} → BrainState n → Region.BrainRegion → BrainThemeConsumerSemanticProfile n

brainThemeConsumerSemanticsSurface : BrainThemeConsumerSemanticsSurface
brainThemeConsumerSemanticsSurface = record
  { themeTransport = ThemeTransport.brainThemeChemistryChannelTransportSurface
  ; themeSemanticTransport = ThemeLaws.brainThemeSemanticTransportLawsSurface
  ; themeEndToEnd = ThemeEnd.brainThemeEndToEndSemanticDepthSurface
  ; consumerProfile = brainThemeConsumerSemanticProfile
  }
