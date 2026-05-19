module Ontology.Brain.BrainSideLocalTheoremLane where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.List.Base using (List; _∷_; [])

import Ontology.Brain.BrainVocabularySurface as Vocabulary
import Ontology.Brain.BrainCoarseSummarySurface as Coarse
import Ontology.Brain.BrainExtractionSurface as Extraction
import Ontology.Brain.BrainInvariantSurface as Invariant
import Ontology.Brain.BrainInvariantDepth as Depth
import Ontology.Brain.BrainInvariantSemanticLaws as Semantics
import Ontology.Brain.BrainThemeConsumerLaws as Theme
import Ontology.Brain.BrainRegionAutomatonSurface as Region
import Ontology.Brain.BrainVisualFormConstantSurface as Visual
import Ontology.Brain.BrainLearningEigenbasisSurface as Learning
import Ontology.Brain.BrainMorphospaceGapJunctionSurface as Morphospace

------------------------------------------------------------------------
-- Brain-side local theorem lane.
--
-- This breaks the "brain is only archive pressure" blockage at the local
-- owner level by bundling the theorem-thin vocabulary, summary, extraction,
-- invariant, invariant-depth, semantics, consumer, automaton, visual-form,
-- learning-profile, and morphospace surfaces.
--
-- It still does not claim a complete biological brain model.

record BrainSideLocalTheoremLane : Setω where
  field
    vocabulary : Vocabulary.BrainVocabularySurface
    coarseSummary : Coarse.BrainCoarseSummarySurface
    extraction : Extraction.BrainExtractionSurface
    invariant : Invariant.BrainInvariantSurface
    invariantDepth : Depth.BrainInvariantDepthSurface
    invariantSemantics : Semantics.BrainInvariantSemanticLawsSurface
    themeConsumer : Theme.BrainThemeConsumerLawSurface
    regionAutomaton : Region.BrainRegionAutomatonSurface
    visualFormConstants : Visual.BrainVisualFormConstantSurface
    learningEigenbasis : Learning.BrainLearningEigenbasisSurface
    morphospaceGapJunctions : Morphospace.BrainMorphospaceGapJunctionSurface

    localizedTheoremLane : ⊤
    notBiologicalClosureTheorem : ⊤

    promotionWouldRequire : List String

brainSideLocalTheoremLane : BrainSideLocalTheoremLane
brainSideLocalTheoremLane = record
  { vocabulary = Vocabulary.brainVocabularySurface
  ; coarseSummary = Coarse.brainCoarseSummarySurface
  ; extraction = Extraction.brainExtractionSurface
  ; invariant = Invariant.brainInvariantSurface
  ; invariantDepth = Depth.brainInvariantDepthSurface
  ; invariantSemantics = Semantics.brainInvariantSemanticLawsSurface
  ; themeConsumer = Theme.brainThemeConsumerLawSurface
  ; regionAutomaton = Region.brainRegionAutomatonSurface
  ; visualFormConstants = Visual.brainVisualFormConstantSurface
  ; learningEigenbasis = Learning.brainLearningEigenbasisSurface
  ; morphospaceGapJunctions = Morphospace.brainMorphospaceGapJunctionSurface
  ; localizedTheoremLane = tt
  ; notBiologicalClosureTheorem = tt
  ; promotionWouldRequire =
      "a local dynamical brain owner, not only static vocabulary/extraction/invariant laws"
      ∷ "a bridge from local brain invariants into the existing closure theorem owner stack"
      ∷ "empirical or mechanistic validation boundaries for any neuroscience interpretation"
      ∷ []
  }
