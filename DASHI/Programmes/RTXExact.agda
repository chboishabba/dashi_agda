module DASHI.Programmes.RTXExact where

open import DASHI.Programmes.ResearchProgrammeExact
open import DASHI.Core.PredictionEnvelopeExact

-- dashiRTX: PDA/MDL light transport, metric/Lyapunov descent, and
-- quadtree/ultrametric refinement experiments.  The generic ultrametric/MDL
-- geometry is formally owned; literal rendering claims remain frontier-facing.

dashiRTXProgramme : ResearchProgramme
dashiRTXProgramme =
  researchProgramme
    dashiRTX
    lightTransportGeometry
    ultrametricMDLGeometry
    corePredictionInference
    frontierAdapter
    true refl
    true refl
    canonicalPredictionEnvelopeBoundary
