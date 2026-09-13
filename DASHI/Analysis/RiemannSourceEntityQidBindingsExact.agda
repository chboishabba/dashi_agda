module DASHI.Analysis.RiemannSourceEntityQidBindingsExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Analysis.DeBruijnNewman2026SourceWeldExact as Source
import DASHI.Wikimedia.ScientificCitationQidBindingsExact as Citation

------------------------------------------------------------------------
-- RIEMANN / DE BRUIJN-NEWMAN SOURCE <-> ENTITY ALIGNMENTS
--
-- This is a literal adapter over the existing DBNSource constructors. The DOI,
-- arXiv identifier or candidate repository remains the source identifier in
-- DeBruijnNewman2026SourceWeldExact; QIDs are related entity metadata only.
------------------------------------------------------------------------

bindingForDBNSource : Source.DBNSource → Citation.CitationEntityBinding
bindingForDBNSource Source.polymath2019 = Citation.polymath2019
bindingForDBNSource Source.plattTrudgian2021 = Citation.plattTrudgian2021
bindingForDBNSource Source.gomila2026Candidate = Citation.gomila2026Candidate

record RiemannReferenceEntityBoundary : Set where
  constructor riemann-reference-entity-boundary
  field
    everyCurrentDBNSourceHasEntityBinding : Bool
    doiArxivOrRepositoryRemainsSourceIdentity : Bool
    qidCreatesCertificateReplay : Bool
    qidCreatesRiemannHypothesisProof : Bool

canonicalRiemannReferenceEntityBoundary : RiemannReferenceEntityBoundary
canonicalRiemannReferenceEntityBoundary =
  riemann-reference-entity-boundary true true false false

data QidPromotesCandidateToPublishedResult : Set where
qidDoesNotPromoteCandidate : QidPromotesCandidateToPublishedResult → ⊥
qidDoesNotPromoteCandidate ()
