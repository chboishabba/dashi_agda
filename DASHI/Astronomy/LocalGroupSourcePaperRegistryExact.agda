module DASHI.Astronomy.LocalGroupSourcePaperRegistryExact where

open import DASHI.Core.Prelude
open import DASHI.Core.AttributedSourceCore
open import DASHI.Astronomy.LocalGroupObservationFrameProvenanceExact

------------------------------------------------------------------------
-- Canonical registry of the four public comparison papers.
------------------------------------------------------------------------

sourcePapers : List AttributedSource
sourcePapers =
  mcConnachie2012
  ∷ kallivayalil2013
  ∷ vasilievBelokurovErkal2021
  ∷ reidBrunthaler2020
  ∷ []

sourcePaperCount : Nat
sourcePaperCount = sourceCount sourcePapers

sourcePaperCountIsFour : sourcePaperCount ≡ 4
sourcePaperCountIsFour = refl
