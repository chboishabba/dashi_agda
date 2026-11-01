module DASHI.Programmes.TestHarnessExact where

open import DASHI.Programmes.ResearchProgrammeExact
open import DASHI.Core.PredictionEnvelopeExact

-- dashitest: heterogeneous experiment harness spanning quotient learning,
-- observers, compression, CA, backend parity, and related diagnostics.
-- It is intentionally not mirrored script-for-script in Agda; the formal
-- attachment is to shared Core semantics plus the experiment-inference layer.

dashitestProgramme : ResearchProgramme
dashitestProgramme =
  researchProgramme
    dashitest
    heterogeneousExperimentHarness
    corePredictionInference
    coreKernelDefectAdmissibility
    semanticAdapter
    true refl
    true refl
    canonicalPredictionEnvelopeBoundary
