module DASHI.Programmes.CoreReferenceExact where

open import DASHI.Programmes.ResearchProgrammeExact
open import DASHI.Core.PredictionEnvelopeExact

-- dashiCORE: executable/reference implementation of the domain-agnostic
-- carrier/kernel/defect/admissibility/MDL substrate.

dashiCOREProgramme : ResearchProgramme
dashiCOREProgramme =
  researchProgramme
    dashiCORE
    coreSemanticReference
    coreKernelDefectAdmissibility
    foundationsClaimTransport
    explicitBridge
    true refl
    true refl
    canonicalPredictionEnvelopeBoundary
