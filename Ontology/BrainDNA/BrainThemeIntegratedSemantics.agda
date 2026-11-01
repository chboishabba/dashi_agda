module Ontology.BrainDNA.BrainThemeIntegratedSemantics where

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
import Ontology.BrainDNA.BrainThemeConsumerLaws as ConsumerLaws
import Ontology.BrainDNA.BrainThemeEndToEndSemanticDepth as ThemeEnd
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)

------------------------------------------------------------------------
-- Bounded integrated semantics surface over the localized brain themes.
--
-- This remains theorem-thin and non-claiming: it packages exact end-to-end
-- theme-facing semantic alignment into the already landed
-- chemistry/channel/handoff boundaries without asserting neuroscience
-- completeness.

record BrainThemeIntegratedSemanticProfile (n : Nat) : Set where
  constructor mkBrainThemeIntegratedSemanticProfile
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

brainThemeIntegratedSemanticProfile :
  ∀ {n} → BrainState n → Region.BrainRegion → BrainThemeIntegratedSemanticProfile n
brainThemeIntegratedSemanticProfile st r =
  mkBrainThemeIntegratedSemanticProfile
    (ConsumerLaws.BrainThemeConsumerLawProfile.lens
      (ConsumerLaws.brainThemeConsumerLawProfile st r))
    (ConsumerLaws.BrainThemeConsumerLawProfile.motif
      (ConsumerLaws.brainThemeConsumerLawProfile st r))
    (ConsumerLaws.BrainThemeConsumerLawProfile.visualClass
      (ConsumerLaws.brainThemeConsumerLawProfile st r))
    (ConsumerLaws.BrainThemeConsumerLawProfile.learningPhase
      (ConsumerLaws.brainThemeConsumerLawProfile st r))
    (ConsumerLaws.BrainThemeConsumerLawProfile.morphSemantic
      (ConsumerLaws.brainThemeConsumerLawProfile st r))
    (ConsumerLaws.BrainThemeConsumerLawProfile.order
      (ConsumerLaws.brainThemeConsumerLawProfile st r))
    (ConsumerLaws.BrainThemeConsumerLawProfile.width
      (ConsumerLaws.brainThemeConsumerLawProfile st r))
    (ConsumerLaws.BrainThemeConsumerLawProfile.emittedAdmissibility
      (ConsumerLaws.brainThemeConsumerLawProfile st r))
    (ConsumerLaws.BrainThemeConsumerLawProfile.recoveryBoundary
      (ConsumerLaws.brainThemeConsumerLawProfile st r))
    (ConsumerLaws.BrainThemeConsumerLawProfile.thermoChecksum
      (ConsumerLaws.brainThemeConsumerLawProfile st r))
    (ConsumerLaws.BrainThemeConsumerLawProfile.hamiltonianChecksum
      (ConsumerLaws.brainThemeConsumerLawProfile st r))
    (ConsumerLaws.BrainThemeConsumerLawProfile.crossBand
      (ConsumerLaws.brainThemeConsumerLawProfile st r))

integratedLensExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeIntegratedSemanticProfile.lens
    (brainThemeIntegratedSemanticProfile st r)
    ≡
  Region.lensOf r
integratedLensExact st r =
  ConsumerLaws.consumerLawLensExact st r

integratedMotifExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeIntegratedSemanticProfile.motif
    (brainThemeIntegratedSemanticProfile st r)
    ≡
  Region.motifOf r
integratedMotifExact st r =
  ConsumerLaws.consumerLawMotifExact st r

integratedVisualClassMatchesEndToEnd :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeIntegratedSemanticProfile.visualClass
    (brainThemeIntegratedSemanticProfile st r)
    ≡
  ThemeEnd.BrainThemeEndToEndSemanticProfile.visualClass
    (ThemeEnd.brainThemeEndToEndSemanticProfile st r)
integratedVisualClassMatchesEndToEnd st r = refl

integratedLearningPhaseMatchesEndToEnd :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeIntegratedSemanticProfile.learningPhase
    (brainThemeIntegratedSemanticProfile st r)
    ≡
  ThemeEnd.BrainThemeEndToEndSemanticProfile.learningPhase
    (ThemeEnd.brainThemeEndToEndSemanticProfile st r)
integratedLearningPhaseMatchesEndToEnd st r = refl

integratedMorphSemanticExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeIntegratedSemanticProfile.morphSemantic
    (brainThemeIntegratedSemanticProfile st r)
    ≡
  Morph.BrainMorphospacePoint.semantic (Morph.morphospaceOfState st)
integratedMorphSemanticExact st r =
  ConsumerLaws.consumerLawMorphSemanticExact st r

integratedOrderLineMajor :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeIntegratedSemanticProfile.order
    (brainThemeIntegratedSemanticProfile st r)
    ≡
  lineMajor
integratedOrderLineMajor st r =
  ConsumerLaws.consumerLawOrderLineMajor st r

integratedWidthExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeIntegratedSemanticProfile.width
    (brainThemeIntegratedSemanticProfile st r)
    ≡
  n
integratedWidthExact st r =
  ConsumerLaws.consumerLawWidthExact st r

integratedRecoveryBoundaryExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeIntegratedSemanticProfile.recoveryBoundary
    (brainThemeIntegratedSemanticProfile st r)
    ≡
  3
integratedRecoveryBoundaryExact st r =
  ConsumerLaws.consumerLawRecoveryBoundaryExact st r

integratedThermoMatchesEndToEnd :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeIntegratedSemanticProfile.thermoChecksum
    (brainThemeIntegratedSemanticProfile st r)
    ≡
  ThemeEnd.BrainThemeEndToEndSemanticProfile.thermoChecksum
    (ThemeEnd.brainThemeEndToEndSemanticProfile st r)
integratedThermoMatchesEndToEnd st r =
  ConsumerLaws.consumerLawThermoMatchesTheme st r

integratedHamiltonianMatchesEndToEnd :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeIntegratedSemanticProfile.hamiltonianChecksum
    (brainThemeIntegratedSemanticProfile st r)
    ≡
  ThemeEnd.BrainThemeEndToEndSemanticProfile.hamiltonianChecksum
    (ThemeEnd.brainThemeEndToEndSemanticProfile st r)
integratedHamiltonianMatchesEndToEnd st r =
  ConsumerLaws.consumerLawHamiltonianMatchesTheme st r

integratedCrossBandMatchesEndToEnd :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeIntegratedSemanticProfile.crossBand
    (brainThemeIntegratedSemanticProfile st r)
    ≡
  ThemeEnd.BrainThemeEndToEndSemanticProfile.crossBand
    (ThemeEnd.brainThemeEndToEndSemanticProfile st r)
integratedCrossBandMatchesEndToEnd st r =
  ConsumerLaws.consumerLawCrossBandMatchesTheme st r

record BrainThemeIntegratedSemanticsSurface : Setω where
  field
    consumerLaws : ConsumerLaws.BrainThemeConsumerLawsSurface
    themeEndToEnd : ThemeEnd.BrainThemeEndToEndSemanticDepthSurface
    integratedProfile :
      ∀ {n} → BrainState n → Region.BrainRegion → BrainThemeIntegratedSemanticProfile n

brainThemeIntegratedSemanticsSurface : BrainThemeIntegratedSemanticsSurface
brainThemeIntegratedSemanticsSurface = record
  { consumerLaws = ConsumerLaws.brainThemeConsumerLawsSurface
  ; themeEndToEnd = ThemeEnd.brainThemeEndToEndSemanticDepthSurface
  ; integratedProfile = brainThemeIntegratedSemanticProfile
  }
