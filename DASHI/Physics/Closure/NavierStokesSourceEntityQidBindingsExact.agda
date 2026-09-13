module DASHI.Physics.Closure.NavierStokesSourceEntityQidBindingsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.ScientificCitationQidBindingsExact as Citation

------------------------------------------------------------------------
-- NAVIER-STOKES SOURCE <-> ENTITY ALIGNMENTS
--
-- This mirrors the live common citation ledger. Exact publication/theorem
-- identity remains in the DOI/bibliography; QIDs annotate related people and
-- concepts only.
------------------------------------------------------------------------

data NSReferenceKey : Set where
  coifmanMeyer lerayHopf bkm ckn leiRenTian2025 ess2003 : NSReferenceKey

bindingForNS : NSReferenceKey → Citation.CitationEntityBinding
bindingForNS coifmanMeyer = Citation.coifmanMeyer
bindingForNS lerayHopf = Citation.lerayHopf
bindingForNS bkm = Citation.bkm
bindingForNS ckn = Citation.ckn
bindingForNS leiRenTian2025 = Citation.leiRenTian2025
bindingForNS ess2003 = Citation.ess2003

record NSReferenceEntityBoundary : Set where
  constructor ns-reference-entity-boundary
  field
    qidsAnnotateSourceSurface : Bool
    exactCriterionStillRequiresCitationLocator : Bool
    qidCreatesContinuationCriterion : Bool
    qidClosesPackageA : Bool

canonicalNSReferenceEntityBoundary : NSReferenceEntityBoundary
canonicalNSReferenceEntityBoundary =
  ns-reference-entity-boundary true true false false

data QidClosesNavierStokesEstimate : Set where
qidDoesNotCloseNavierStokesEstimate : QidClosesNavierStokesEstimate → ⊥
qidDoesNotCloseNavierStokesEstimate ()
