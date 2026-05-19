module Ontology.BrainDNA.BrainThemeEndToEndSemanticDepth where

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
import Ontology.BrainDNA.BrainConnectorEndToEndSemanticDepth as EndToEnd
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)

------------------------------------------------------------------------
-- Bounded end-to-end semantic-depth surface keyed by the localized theme
-- owners. This remains theorem-thin and non-claiming: it only packages
-- exact alignment witnesses already owned by the current theme transport,
-- semantic transport, and connector end-to-end semantic-depth layers.

record BrainThemeEndToEndSemanticProfile (n : Nat) : Set where
  constructor mkBrainThemeEndToEndSemanticProfile
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

brainThemeEndToEndSemanticProfile :
  ∀ {n} → BrainState n → Region.BrainRegion → BrainThemeEndToEndSemanticProfile n
brainThemeEndToEndSemanticProfile st r =
  mkBrainThemeEndToEndSemanticProfile
    (ThemeLaws.BrainThemeSemanticTransportProfile.lens
      (ThemeLaws.brainThemeSemanticTransportProfile st r))
    (ThemeLaws.BrainThemeSemanticTransportProfile.motif
      (ThemeLaws.brainThemeSemanticTransportProfile st r))
    (ThemeLaws.BrainThemeSemanticTransportProfile.visualClass
      (ThemeLaws.brainThemeSemanticTransportProfile st r))
    (ThemeLaws.BrainThemeSemanticTransportProfile.learningPhase
      (ThemeLaws.brainThemeSemanticTransportProfile st r))
    (ThemeLaws.BrainThemeSemanticTransportProfile.morphSemantic
      (ThemeLaws.brainThemeSemanticTransportProfile st r))
    (EndToEnd.BrainConnectorEndToEndSemanticProfile.order
      (EndToEnd.brainConnectorEndToEndSemanticProfile st r))
    (EndToEnd.BrainConnectorEndToEndSemanticProfile.width
      (EndToEnd.brainConnectorEndToEndSemanticProfile st r))
    (EndToEnd.BrainConnectorEndToEndSemanticProfile.emittedAdmissibility
      (EndToEnd.brainConnectorEndToEndSemanticProfile st r))
    (EndToEnd.BrainConnectorEndToEndSemanticProfile.recoveryBoundary
      (EndToEnd.brainConnectorEndToEndSemanticProfile st r))
    (ThemeLaws.BrainThemeSemanticTransportProfile.thermoChecksum
      (ThemeLaws.brainThemeSemanticTransportProfile st r))
    (ThemeLaws.BrainThemeSemanticTransportProfile.hamiltonianChecksum
      (ThemeLaws.brainThemeSemanticTransportProfile st r))
    (EndToEnd.BrainConnectorEndToEndSemanticProfile.crossBand
      (EndToEnd.brainConnectorEndToEndSemanticProfile st r))

themeEndToEndLensExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeEndToEndSemanticProfile.lens
    (brainThemeEndToEndSemanticProfile st r)
    ≡
  Region.lensOf r
themeEndToEndLensExact st r =
  ThemeLaws.themeSemanticTransportLensExact st r

themeEndToEndMotifExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeEndToEndSemanticProfile.motif
    (brainThemeEndToEndSemanticProfile st r)
    ≡
  Region.motifOf r
themeEndToEndMotifExact st r =
  ThemeLaws.themeSemanticTransportMotifExact st r

themeEndToEndVisualWidthExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeEndToEndSemanticProfile.width
    (brainThemeEndToEndSemanticProfile st r)
    ≡
  n
themeEndToEndVisualWidthExact st r =
  EndToEnd.endToEndWidthMatchesThemeTransport st r

themeEndToEndLearningWidthExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  Learn.BrainLearningEigenbasisProfile.width
    (Learn.profileOfState st)
    ≡
  BrainThemeEndToEndSemanticProfile.width
    (brainThemeEndToEndSemanticProfile st r)
themeEndToEndLearningWidthExact st r =
  ThemeLaws.themeSemanticTransportLearningPhaseWidthExact st r

themeEndToEndMorphSemanticExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeEndToEndSemanticProfile.morphSemantic
    (brainThemeEndToEndSemanticProfile st r)
    ≡
  Morph.BrainMorphospacePoint.semantic (Morph.morphospaceOfState st)
themeEndToEndMorphSemanticExact st r =
  ThemeLaws.themeSemanticTransportMorphSemanticExact st r

themeEndToEndOrderLineMajor :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeEndToEndSemanticProfile.order
    (brainThemeEndToEndSemanticProfile st r)
    ≡
  lineMajor
themeEndToEndOrderLineMajor st r =
  EndToEnd.endToEndOrderLineMajor st r

themeEndToEndRecoveryBoundaryExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeEndToEndSemanticProfile.recoveryBoundary
    (brainThemeEndToEndSemanticProfile st r)
    ≡
  3
themeEndToEndRecoveryBoundaryExact st r =
  EndToEnd.endToEndRecoveryBoundaryExact st r

themeEndToEndThermoMatchesThemeTransport :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeEndToEndSemanticProfile.thermoChecksum
    (brainThemeEndToEndSemanticProfile st r)
    ≡
  ThemeLaws.BrainThemeSemanticTransportProfile.thermoChecksum
    (ThemeLaws.brainThemeSemanticTransportProfile st r)
themeEndToEndThermoMatchesThemeTransport st r = refl

themeEndToEndHamiltonianMatchesThemeTransport :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeEndToEndSemanticProfile.hamiltonianChecksum
    (brainThemeEndToEndSemanticProfile st r)
    ≡
  ThemeLaws.BrainThemeSemanticTransportProfile.hamiltonianChecksum
    (ThemeLaws.brainThemeSemanticTransportProfile st r)
themeEndToEndHamiltonianMatchesThemeTransport st r = refl

themeEndToEndCrossBandMatchesThemeTransport :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeEndToEndSemanticProfile.crossBand
    (brainThemeEndToEndSemanticProfile st r)
    ≡
  ThemeLaws.BrainThemeSemanticTransportProfile.crossBand
    (ThemeLaws.brainThemeSemanticTransportProfile st r)
themeEndToEndCrossBandMatchesThemeTransport st r =
  ThemeLaws.themeSemanticTransportCrossBandMatchesHandoff st r

record BrainThemeEndToEndSemanticDepthSurface : Setω where
  field
    themeTransport : ThemeTransport.BrainThemeChemistryChannelTransportSurface
    themeSemanticTransport : ThemeLaws.BrainThemeSemanticTransportLawsSurface
    connectorEndToEnd : EndToEnd.BrainConnectorEndToEndSemanticDepthSurface
    semanticProfile :
      ∀ {n} → BrainState n → Region.BrainRegion → BrainThemeEndToEndSemanticProfile n

brainThemeEndToEndSemanticDepthSurface :
  BrainThemeEndToEndSemanticDepthSurface
brainThemeEndToEndSemanticDepthSurface = record
  { themeTransport = ThemeTransport.brainThemeChemistryChannelTransportSurface
  ; themeSemanticTransport = ThemeLaws.brainThemeSemanticTransportLawsSurface
  ; connectorEndToEnd = EndToEnd.brainConnectorEndToEndSemanticDepthSurface
  ; semanticProfile = brainThemeEndToEndSemanticProfile
  }
