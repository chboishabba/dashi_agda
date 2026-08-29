module DASHI.Programmes.BrainExact where

open import DASHI.Programmes.ResearchProgrammeExact
open import DASHI.Core.PredictionEnvelopeExact

-- dashiBRAIN: hemibrain/connectome kernel-closure and coarse-graining lab.
-- The abstract network/kernel semantics are owned; the literal hemibrain
-- instantiation remains a domain-facing semantic adapter rather than a theorem
-- claim about the dataset.

dashiBRAINProgramme : ResearchProgramme
dashiBRAINProgramme =
  researchProgramme
    dashiBRAIN
    connectomeKernelClosure
    biologyNetworkGeometry
    coreKernelDefectAdmissibility
    semanticAdapter
    true refl
    true refl
    canonicalPredictionEnvelopeBoundary
