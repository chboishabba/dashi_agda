module DASHI.Programmes.GrokkingExact where

open import DASHI.Programmes.ResearchProgrammeExact
open import DASHI.Core.PredictionEnvelopeExact
import DASHI.Learning.GrokkingCircuitTemporalAlignmentExact

-- DASHIg: Phase-2 external validation and architecture comparison for grokking.
-- Its natural formal owner is the Stage-6/7 calibration and experiment layer.
-- The circuit temporal-alignment receipt is registered here as an explicit
-- calibration/experiment seam; it does not alter the programme's core owner,
-- kernel admissibility owner, coverage depth, or promotion boundary.

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
