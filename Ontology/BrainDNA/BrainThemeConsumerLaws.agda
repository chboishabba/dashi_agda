module Ontology.BrainDNA.BrainThemeConsumerLaws where

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
import Ontology.BrainDNA.BrainThemeConsumerSemantics as ConsumerSem
import Ontology.BrainDNA.BrainThemeSemanticTransportLaws as ThemeLaws
import Ontology.BrainDNA.BrainThemeEndToEndSemanticDepth as ThemeEnd
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)

------------------------------------------------------------------------
-- Bounded downstream consumer-law surface over the localized theme lane.
--
-- This remains theorem-thin and non-claiming: it exposes exact alignment
-- from region/visual/learning/morphospace theme profiles into the already
-- landed downstream consumer boundaries.

record BrainThemeConsumerLawProfile (n : Nat) : Set where
  constructor mkBrainThemeConsumerLawProfile
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

brainThemeConsumerLawProfile :
  ∀ {n} → BrainState n → Region.BrainRegion → BrainThemeConsumerLawProfile n
brainThemeConsumerLawProfile st r =
  mkBrainThemeConsumerLawProfile
    (ConsumerSem.BrainThemeConsumerSemanticProfile.lens
      (ConsumerSem.brainThemeConsumerSemanticProfile st r))
    (ConsumerSem.BrainThemeConsumerSemanticProfile.motif
      (ConsumerSem.brainThemeConsumerSemanticProfile st r))
    (ConsumerSem.BrainThemeConsumerSemanticProfile.visualClass
      (ConsumerSem.brainThemeConsumerSemanticProfile st r))
    (ConsumerSem.BrainThemeConsumerSemanticProfile.learningPhase
      (ConsumerSem.brainThemeConsumerSemanticProfile st r))
    (ConsumerSem.BrainThemeConsumerSemanticProfile.morphSemantic
      (ConsumerSem.brainThemeConsumerSemanticProfile st r))
    (ConsumerSem.BrainThemeConsumerSemanticProfile.order
      (ConsumerSem.brainThemeConsumerSemanticProfile st r))
    (ConsumerSem.BrainThemeConsumerSemanticProfile.width
      (ConsumerSem.brainThemeConsumerSemanticProfile st r))
    (ConsumerSem.BrainThemeConsumerSemanticProfile.emittedAdmissibility
      (ConsumerSem.brainThemeConsumerSemanticProfile st r))
    (ConsumerSem.BrainThemeConsumerSemanticProfile.recoveryBoundary
      (ConsumerSem.brainThemeConsumerSemanticProfile st r))
    (ConsumerSem.BrainThemeConsumerSemanticProfile.thermoChecksum
      (ConsumerSem.brainThemeConsumerSemanticProfile st r))
    (ConsumerSem.BrainThemeConsumerSemanticProfile.hamiltonianChecksum
      (ConsumerSem.brainThemeConsumerSemanticProfile st r))
    (ConsumerSem.BrainThemeConsumerSemanticProfile.crossBand
      (ConsumerSem.brainThemeConsumerSemanticProfile st r))

consumerLawLensExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeConsumerLawProfile.lens
    (brainThemeConsumerLawProfile st r)
    ≡
  Region.lensOf r
consumerLawLensExact st r =
  ConsumerSem.consumerLensExact st r

consumerLawMotifExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeConsumerLawProfile.motif
    (brainThemeConsumerLawProfile st r)
    ≡
  Region.motifOf r
consumerLawMotifExact st r =
  ConsumerSem.consumerMotifExact st r

consumerLawVisualClassMatchesTheme :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeConsumerLawProfile.visualClass
    (brainThemeConsumerLawProfile st r)
    ≡
  ThemeLaws.BrainThemeSemanticTransportProfile.visualClass
    (ThemeLaws.brainThemeSemanticTransportProfile st r)
consumerLawVisualClassMatchesTheme st r =
  ConsumerSem.consumerVisualClassMatchesTheme st r

consumerLawLearningPhaseMatchesTheme :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeConsumerLawProfile.learningPhase
    (brainThemeConsumerLawProfile st r)
    ≡
  ThemeLaws.BrainThemeSemanticTransportProfile.learningPhase
    (ThemeLaws.brainThemeSemanticTransportProfile st r)
consumerLawLearningPhaseMatchesTheme st r =
  ConsumerSem.consumerLearningPhaseMatchesTheme st r

consumerLawMorphSemanticExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeConsumerLawProfile.morphSemantic
    (brainThemeConsumerLawProfile st r)
    ≡
  Morph.BrainMorphospacePoint.semantic (Morph.morphospaceOfState st)
consumerLawMorphSemanticExact st r =
  ConsumerSem.consumerMorphSemanticExact st r

consumerLawOrderLineMajor :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeConsumerLawProfile.order
    (brainThemeConsumerLawProfile st r)
    ≡
  lineMajor
consumerLawOrderLineMajor st r =
  ConsumerSem.consumerOrderLineMajor st r

consumerLawWidthExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeConsumerLawProfile.width
    (brainThemeConsumerLawProfile st r)
    ≡
  n
consumerLawWidthExact st r =
  ConsumerSem.consumerWidthExact st r

consumerLawRecoveryBoundaryExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeConsumerLawProfile.recoveryBoundary
    (brainThemeConsumerLawProfile st r)
    ≡
  3
consumerLawRecoveryBoundaryExact st r =
  ConsumerSem.consumerRecoveryBoundaryExact st r

consumerLawThermoMatchesTheme :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeConsumerLawProfile.thermoChecksum
    (brainThemeConsumerLawProfile st r)
    ≡
  ThemeEnd.BrainThemeEndToEndSemanticProfile.thermoChecksum
    (ThemeEnd.brainThemeEndToEndSemanticProfile st r)
consumerLawThermoMatchesTheme st r =
  ConsumerSem.consumerThermoChecksumMatchesTheme st r

consumerLawHamiltonianMatchesTheme :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeConsumerLawProfile.hamiltonianChecksum
    (brainThemeConsumerLawProfile st r)
    ≡
  ThemeEnd.BrainThemeEndToEndSemanticProfile.hamiltonianChecksum
    (ThemeEnd.brainThemeEndToEndSemanticProfile st r)
consumerLawHamiltonianMatchesTheme st r =
  ConsumerSem.consumerHamiltonianMatchesTheme st r

consumerLawCrossBandMatchesTheme :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeConsumerLawProfile.crossBand
    (brainThemeConsumerLawProfile st r)
    ≡
  ThemeEnd.BrainThemeEndToEndSemanticProfile.crossBand
    (ThemeEnd.brainThemeEndToEndSemanticProfile st r)
consumerLawCrossBandMatchesTheme st r =
  ConsumerSem.consumerCrossBandMatchesTheme st r

record BrainThemeConsumerLawsSurface : Setω where
  field
    consumerSemantics : ConsumerSem.BrainThemeConsumerSemanticsSurface
    themeSemanticTransport : ThemeLaws.BrainThemeSemanticTransportLawsSurface
    themeEndToEnd : ThemeEnd.BrainThemeEndToEndSemanticDepthSurface
    consumerLawProfile :
      ∀ {n} → BrainState n → Region.BrainRegion → BrainThemeConsumerLawProfile n

brainThemeConsumerLawsSurface : BrainThemeConsumerLawsSurface
brainThemeConsumerLawsSurface = record
  { consumerSemantics = ConsumerSem.brainThemeConsumerSemanticsSurface
  ; themeSemanticTransport = ThemeLaws.brainThemeSemanticTransportLawsSurface
  ; themeEndToEnd = ThemeEnd.brainThemeEndToEndSemanticDepthSurface
  ; consumerLawProfile = brainThemeConsumerLawProfile
  }
