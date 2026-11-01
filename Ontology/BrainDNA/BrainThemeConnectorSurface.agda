module Ontology.BrainDNA.BrainThemeConnectorSurface where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
open import Ontology.Brain.BrainInvariantSurface using (BrainCarrierInvariant)
import Ontology.Brain.BrainRegionAutomatonSurface as Region
import Ontology.Brain.BrainVisualFormConstantSurface as Visual
import Ontology.Brain.BrainLearningEigenbasisSurface as Learn
import Ontology.Brain.BrainMorphospaceGapJunctionSurface as Morph
import Ontology.BrainDNA.BrainVocabularyPacketCompatibility as Packet
import Ontology.BrainDNA.BrainExtractionConnectorSemantics as ExtractSem
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)

------------------------------------------------------------------------
-- Bounded connector that consumes the four local brain theme owners into
-- the current BrainDNA crossover side.
--
-- This remains theorem-thin and non-claiming: it packages typed theme
-- profiles and exact transport/coherence witnesses over the existing local
-- packet/extraction connector surfaces. It does not claim a realistic
-- representation map or complete neuroscience semantics.

record BrainThemeProfile (n : Nat) : Set where
  constructor brainThemeProfile
  field
    regionCorrespondence : Region.RegionCorrespondence
    visualGeometry : Visual.BrainLogPolarGeometry
    visualClass : Visual.BrainVisualFormConstant
    learningProfile : Learn.BrainLearningEigenbasisProfile
    morphospacePoint : Morph.BrainMorphospacePoint
    extractionSemantics : ExtractSem.BrainExtractionConnectorSemantics n
    packetOrder : ScanOrder

themeProfileOf :
  ∀ {n} → BrainState n → Region.BrainRegion → BrainThemeProfile n
themeProfileOf st r =
  brainThemeProfile
    (Region.correspondenceOf r)
    (Visual.geometryOfState st)
    (Visual.classifyState st)
    (Learn.profileOfState st)
    (Morph.morphospaceOfState st)
    (ExtractSem.brainExtractionConnectorSemantics st)
    (Packet.BrainVocabularyPacketCompatibilitySurface.packetOrderCompatible
      Packet.brainVocabularyPacketCompatibilitySurface st)

themeRegionLensExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  Region.RegionCorrespondence.lens
    (BrainThemeProfile.regionCorrespondence (themeProfileOf st r))
    ≡
  Region.lensOf r
themeRegionLensExact st r = Region.correspondence-lens-exact r

themeRegionMotifExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  Region.RegionCorrespondence.motif
    (BrainThemeProfile.regionCorrespondence (themeProfileOf st r))
    ≡
  Region.motifOf r
themeRegionMotifExact st r = Region.correspondence-motif-exact r

themeVisualWidthExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  Visual.BrainLogPolarGeometry.radialRing
    (BrainThemeProfile.visualGeometry (themeProfileOf st r))
    ≡
  n
themeVisualWidthExact st r = Visual.geometry-width st

themeLearningWidthExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  Learn.BrainLearningEigenbasisProfile.width
    (BrainThemeProfile.learningProfile (themeProfileOf st r))
    ≡
  n
themeLearningWidthExact st r = Learn.profile-width-exact st

themeMorphospaceWidthExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  Morph.BrainMorphospacePoint.width
    (BrainThemeProfile.morphospacePoint (themeProfileOf st r))
    ≡
  n
themeMorphospaceWidthExact st r = Morph.state-morphospace-width-exact st

themeExtractionWidthExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainCarrierInvariant.width
    (ExtractSem.BrainExtractionConnectorSemantics.invariant
      (BrainThemeProfile.extractionSemantics (themeProfileOf st r)))
    ≡
  n
themeExtractionWidthExact st r =
  ExtractSem.brainExtractionConnectorSemanticsWidthExact st

themeExtractionOrderLineMajor :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  ExtractSem.BrainExtractionConnectorSemantics.order
    (BrainThemeProfile.extractionSemantics (themeProfileOf st r))
    ≡
  lineMajor
themeExtractionOrderLineMajor st r =
  ExtractSem.brainExtractionConnectorSemanticsOrderLineMajor st

themePacketOrderLineMajor :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainThemeProfile.packetOrder (themeProfileOf st r) ≡ lineMajor
themePacketOrderLineMajor st r =
  Packet.statePacketOrder-lineMajor st

record BrainThemeConnectorSurface : Set₂ where
  field
    regionSurface : Region.BrainRegionAutomatonSurface
    visualSurface : Visual.BrainVisualFormConstantSurface
    learningSurface : Learn.BrainLearningEigenbasisSurface
    morphospaceSurface : Morph.BrainMorphospaceGapJunctionSurface
    packetCompatibility : Packet.BrainVocabularyPacketCompatibilitySurface
    extractionSemanticsSurface : ExtractSem.BrainExtractionConnectorSemanticsSurface
    profile : ∀ {n} → BrainState n → Region.BrainRegion → BrainThemeProfile n

brainThemeConnectorSurface : BrainThemeConnectorSurface
brainThemeConnectorSurface = record
  { regionSurface = Region.brainRegionAutomatonSurface
  ; visualSurface = Visual.brainVisualFormConstantSurface
  ; learningSurface = Learn.brainLearningEigenbasisSurface
  ; morphospaceSurface = Morph.brainMorphospaceGapJunctionSurface
  ; packetCompatibility = Packet.brainVocabularyPacketCompatibilitySurface
  ; extractionSemanticsSurface = ExtractSem.brainExtractionConnectorSemanticsSurface
  ; profile = themeProfileOf
  }
