module DASHI.Physics.Closure.NSTriadKNGrafakosOhDiagonalConvolutionAudit where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Loukas Grafakos; Seungly Oh.
-- Title: "The Kato-Ponce Inequality".
-- Venue/year: Communications in Partial Differential Equations 39 (2014),
-- no. 6, 1128--1157.
-- DOI: 10.1080/03605302.2013.822885.
-- arXiv/DataCite DOI: 10.48550/arXiv.1303.5144.
-- Uses: the comparable-frequency diagonal contribution, Littlewood--Paley
-- square functions, and discrete Cauchy--Schwarz in the frequency-index sum.
-- Relationship: validates the proof pattern used by the direct Stage-3
-- low-output convolution route.  It does not contain the repository's
-- Galerkin, orbit, helicity, or exact shell theorem and is not consumed as the
-- missing first-adjoint estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

data SourceRole : Set where
  proofPatternAnchor repositoryTheorem : SourceRole

grafakosOhRole : SourceRole
grafakosOhRole = proofPatternAnchor

record GrafakosOhScopeReceipt : Set where
  constructor receipt
  field
    peerReviewedArticle : Bool
    comparableFrequencyDiagonalAnalysed : Bool
    squareFunctionAndCauchySchwarzUsed : Bool
    periodicGalerkinCutoffAddressed : Bool
    orbitHelicityTransportAddressed : Bool
    exactFirstAdjointShellTheoremSupplied : Bool

open GrafakosOhScopeReceipt public

grafakosOhScopeReceipt : GrafakosOhScopeReceipt
grafakosOhScopeReceipt = receipt true true true false false false

grafakosOhBibliographyVerified : Bool
grafakosOhBibliographyVerified = true

grafakosOhBibliographyVerifiedIsTrue :
  grafakosOhBibliographyVerified ≡ true
grafakosOhBibliographyVerifiedIsTrue = refl

grafakosOhConsumedAsRepositoryTheorem : Bool
grafakosOhConsumedAsRepositoryTheorem = false

grafakosOhConsumedAsRepositoryTheoremIsFalse :
  grafakosOhConsumedAsRepositoryTheorem ≡ false
grafakosOhConsumedAsRepositoryTheoremIsFalse = refl
