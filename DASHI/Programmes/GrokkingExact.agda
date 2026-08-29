module DASHI.Programmes.GrokkingExact where

open import DASHI.Programmes.ResearchProgrammeExact
open import DASHI.Core.PredictionEnvelopeExact

-- DASHIg: Phase-2 external validation and architecture comparison for grokking.
-- Its natural formal owner is the Stage-6/7 calibration and experiment layer.

DASHIgProgramme : ResearchProgramme
DASHIgProgramme =
  researchProgramme
    DASHIg
    grokkingValidation
    corePredictionInference
    coreKernelDefectAdmissibility
    explicitBridge
    true refl
    true refl
    canonicalPredictionEnvelopeBoundary
