module DASHI.Programmes.DashifineExact where

open import DASHI.Programmes.ResearchProgrammeExact
open import DASHI.Core.PredictionEnvelopeExact

-- dashifine: spectral kernels, quotient/projection geometry, operator learning,
-- and Phase-1 grokking experiments.  Experimental laws are receipt-gated and
-- remain distinct from theorem-grade universality claims.

dashifineProgramme : ResearchProgramme
dashifineProgramme =
  researchProgramme
    dashifine
    spectralLearningGeometry
    coreKernelDefectAdmissibility
    corePredictionInference
    explicitBridge
    true refl
    true refl
    canonicalPredictionEnvelopeBoundary
