module DASHI.Programmes.CFDExact where

open import DASHI.Programmes.ResearchProgrammeExact
open import DASHI.Core.PredictionEnvelopeExact

-- dashiCFD: numerical NS/LES/vorticity/cascade laboratory.
-- Formal ownership is theorem-deep on the Navier-Stokes closure spine; the
-- experiment/inference layer remains the secondary owner for evidence intake.

dashiCFDProgramme : ResearchProgramme
dashiCFDProgramme =
  researchProgramme
    dashiCFD
    fluidClosure
    navierStokesClosure
    corePredictionInference
    theoremDeep
    true refl
    true refl
    canonicalPredictionEnvelopeBoundary
