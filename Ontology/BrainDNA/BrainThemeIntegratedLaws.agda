module Ontology.BrainDNA.BrainThemeIntegratedLaws where

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
import Ontology.BrainDNA.BrainThemeIntegratedSemantics as Integrated
import Ontology.BrainDNA.BrainThemeConsumerLaws as ConsumerLaws
import Ontology.BrainDNA.BrainThemeEndToEndSemanticDepth as ThemeEnd
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)

------------------------------------------------------------------------
-- Bounded integrated law surface over the localized brain themes.
--
-- This remains theorem-thin and non-claiming: it exposes exact integrated
-- theme alignment laws into the already landed chemistry/channel/handoff
-- boundaries, without asserting neuroscience completeness.

record BrainThemeIntegratedLawProfile (n : Nat) : Set where
  constructor mkBrainThemeIntegratedLawProfile
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

brainThemeIntegratedLawProfile :
  ∀ {n} → BrainState n → Region.BrainRegion → BrainThemeIntegratedLawProfile n
brainThemeIntegratedLawProfile st r =
  mkBrainThemeIntegratedLawProfile
    (Integrated.BrainThemeIntegratedSemanticProfile.lens
      (Integrated.brainThemeIntegratedSemanticProfile st r))
    (Integrated.BrainThemeIntegratedSemanticProfile.motif
      (Integrated.brainThemeIntegratedSemanticProfile st r))
    (Integrated.BrainThemeIntegratedSemanticProfile.visualClass
      (Integrated.brainThemeIntegratedSemanticProfile st r))
    (Integrated.BrainThemeIntegratedSemanticProfile.learningPhase
      (Integrated.brainThemeIntegratedSemanticProfile st r))
    (Integrated.BrainThemeIntegratedSemanticProfile.morphSemantic
      (Integrated.brainThemeIntegratedSemanticProfile st r))
    (Integrated.BrainThemeIntegratedSemanticProfile.order
      (Integrated.brainThemeIntegratedSemanticProfile st r))
    (Integrated.BrainThemeIntegratedSemanticProfile.width
      (Integrated.brainThemeIntegratedSemanticProfile st r))
    (Integrated.BrainThemeIntegratedSemanticProfile.emittedAdmissibility
      (Integrated.brainThemeIntegratedSemanticProfile st r))
    (Integrated.BrainThemeIntegratedSemanticProfile.recoveryBoundary
      (Integrated.brainThemeIntegratedSemanticProfile st r))
    (Integrated.BrainThemeIntegratedSemanticProfile.thermoChecksum
      (Integrated.brainThemeIntegratedSemanticProfile st r))
    (Integrated.BrainThemeIntegratedSemanticProfile.hamiltonianChecksum
      (Integrated.brainThemeIntegratedSemanticProfile st r))
    (Integrated.BrainThemeIntegratedSemanticProfile.crossBand
      (Integrated.brainThemeIntegratedSemanticProfile st r))

integratedLawLensExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeIntegratedLawProfile.lens
    (brainThemeIntegratedLawProfile st r)
    ≡
  Region.lensOf r
integratedLawLensExact st r =
  Integrated.integratedLensExact st r

integratedLawMotifExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeIntegratedLawProfile.motif
    (brainThemeIntegratedLawProfile st r)
    ≡
  Region.motifOf r
integratedLawMotifExact st r =
  Integrated.integratedMotifExact st r

integratedLawVisualClassMatchesConsumer :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeIntegratedLawProfile.visualClass
    (brainThemeIntegratedLawProfile st r)
    ≡
  ConsumerLaws.BrainThemeConsumerLawProfile.visualClass
    (ConsumerLaws.brainThemeConsumerLawProfile st r)
integratedLawVisualClassMatchesConsumer st r = refl

integratedLawLearningPhaseMatchesConsumer :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeIntegratedLawProfile.learningPhase
    (brainThemeIntegratedLawProfile st r)
    ≡
  ConsumerLaws.BrainThemeConsumerLawProfile.learningPhase
    (ConsumerLaws.brainThemeConsumerLawProfile st r)
integratedLawLearningPhaseMatchesConsumer st r = refl

integratedLawMorphSemanticExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeIntegratedLawProfile.morphSemantic
    (brainThemeIntegratedLawProfile st r)
    ≡
  Morph.BrainMorphospacePoint.semantic (Morph.morphospaceOfState st)
integratedLawMorphSemanticExact st r =
  Integrated.integratedMorphSemanticExact st r

integratedLawOrderLineMajor :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeIntegratedLawProfile.order
    (brainThemeIntegratedLawProfile st r)
    ≡
  lineMajor
integratedLawOrderLineMajor st r =
  Integrated.integratedOrderLineMajor st r

integratedLawWidthExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeIntegratedLawProfile.width
    (brainThemeIntegratedLawProfile st r)
    ≡
  n
integratedLawWidthExact st r =
  Integrated.integratedWidthExact st r

integratedLawRecoveryBoundaryExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeIntegratedLawProfile.recoveryBoundary
    (brainThemeIntegratedLawProfile st r)
    ≡
  3
integratedLawRecoveryBoundaryExact st r =
  Integrated.integratedRecoveryBoundaryExact st r

integratedLawThermoMatchesEndToEnd :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeIntegratedLawProfile.thermoChecksum
    (brainThemeIntegratedLawProfile st r)
    ≡
  ThemeEnd.BrainThemeEndToEndSemanticProfile.thermoChecksum
    (ThemeEnd.brainThemeEndToEndSemanticProfile st r)
integratedLawThermoMatchesEndToEnd st r =
  Integrated.integratedThermoMatchesEndToEnd st r

integratedLawHamiltonianMatchesEndToEnd :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeIntegratedLawProfile.hamiltonianChecksum
    (brainThemeIntegratedLawProfile st r)
    ≡
  ThemeEnd.BrainThemeEndToEndSemanticProfile.hamiltonianChecksum
    (ThemeEnd.brainThemeEndToEndSemanticProfile st r)
integratedLawHamiltonianMatchesEndToEnd st r =
  Integrated.integratedHamiltonianMatchesEndToEnd st r

integratedLawCrossBandMatchesEndToEnd :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeIntegratedLawProfile.crossBand
    (brainThemeIntegratedLawProfile st r)
    ≡
  ThemeEnd.BrainThemeEndToEndSemanticProfile.crossBand
    (ThemeEnd.brainThemeEndToEndSemanticProfile st r)
integratedLawCrossBandMatchesEndToEnd st r =
  Integrated.integratedCrossBandMatchesEndToEnd st r

record BrainThemeIntegratedLawsSurface : Setω where
  field
    integratedSemantics : Integrated.BrainThemeIntegratedSemanticsSurface
    consumerLaws : ConsumerLaws.BrainThemeConsumerLawsSurface
    themeEndToEnd : ThemeEnd.BrainThemeEndToEndSemanticDepthSurface
    integratedLawProfile :
      ∀ {n} → BrainState n → Region.BrainRegion → BrainThemeIntegratedLawProfile n

brainThemeIntegratedLawsSurface : BrainThemeIntegratedLawsSurface
brainThemeIntegratedLawsSurface = record
  { integratedSemantics = Integrated.brainThemeIntegratedSemanticsSurface
  ; consumerLaws = ConsumerLaws.brainThemeConsumerLawsSurface
  ; themeEndToEnd = ThemeEnd.brainThemeEndToEndSemanticDepthSurface
  ; integratedLawProfile = brainThemeIntegratedLawProfile
  }
