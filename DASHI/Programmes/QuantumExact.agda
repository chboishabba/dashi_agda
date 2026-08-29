module DASHI.Programmes.QuantumExact where

open import DASHI.Programmes.ResearchProgrammeExact
open import DASHI.Core.PredictionEnvelopeExact

-- dashiQ: projection/covariance/MDL and quantum-facing physical hypotheses.
-- Physics Foundations owns the physical claim boundary; Stage-6/7 inference
-- owns experiment design, identifiability, and discrimination semantics.

dashiQProgramme : ResearchProgramme
dashiQProgramme =
  researchProgramme
    dashiQ
    quantumProjectionPhysics
    physicsFoundations
    corePredictionInference
    frontierAdapter
    true refl
    true refl
    canonicalPredictionEnvelopeBoundary
