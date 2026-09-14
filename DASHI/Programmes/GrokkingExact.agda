module DASHI.Programmes.GrokkingExact where

open import DASHI.Programmes.ResearchProgrammeExact
open import DASHI.Core.PredictionEnvelopeExact
import DASHI.Learning.GrokkingCircuitTemporalAlignmentExact
import DASHI.Learning.Mod97CircuitRuntimeBoundaryExact

-- DASHIg: Phase-2 external validation and architecture comparison for grokking.
-- Its natural formal owner is the Stage-6/7 calibration and experiment layer.
-- The circuit temporal-alignment receipt and Mod97 runtime-producer frontier are
-- registered here as explicit calibration/experiment seams. Producer existence
-- does not pay execution, historical-run identity, beta maximality, mechanism,
-- or alter the programme's core owner / kernel admissibility / promotion boundary.

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
