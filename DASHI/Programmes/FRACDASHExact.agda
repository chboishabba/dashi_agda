module DASHI.Programmes.FRACDASHExact where

open import DASHI.Programmes.ResearchProgrammeExact
open import DASHI.Core.PredictionEnvelopeExact

-- FRACDASH: executable semantics-preserving DASHI/FRACTRAN compilation and
-- bridge witnesses.  This programme already has explicit cross-pollination and
-- claim-transport ownership in Foundations.

FRACDASHProgramme : ResearchProgramme
FRACDASHProgramme =
  researchProgramme
    FRACDASH
    executableCompilation
    fractranCrossPollination
    foundationsClaimTransport
    theoremDeep
    true refl
    true refl
    canonicalPredictionEnvelopeBoundary
