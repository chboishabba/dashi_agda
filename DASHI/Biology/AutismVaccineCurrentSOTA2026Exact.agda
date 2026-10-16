module DASHI.Biology.AutismVaccineCurrentSOTA2026Exact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- CURRENT VACCINE/AUTISM SOTA UPDATE (2026)
--
-- The source below updates the scientific evidence window. It is broader than
-- Hbomberguy's MMR-specific claim, so compatibility of direction is retained
-- without pretending exact claim/estimand identity.
------------------------------------------------------------------------

who2026VaccineAutismEvidenceReview : Source.AttributedSource
who2026VaccineAutismEvidenceReview =
  Source.mkNoDOISource
    "World Health Organization"
    "Vaccines, thiomersal and autism spectrum disorder: evidence review 2010-2025"
    "World Health Organization evidence review; ISBN 978-92-4-012353-3"
    "2026"
    "https://www.who.int/publications/i/item/9789240123533"
    Source.institutionalSource
    "Systematic evidence review covering peer-reviewed studies from 2010 through August 2025. WHO reports that the most methodologically rigorous primary studies and included meta-analyses do not support a causal association between vaccines, including thiomersal-containing vaccines, and ASD. This broader institutional review is compatible with the no-causal-link direction but does not automatically become the exact MMR-specific Hbomberguy estimand or a universal zero-risk theorem."
    Source.publicAttribution

record AutismVaccineCurrentSOTABoundary : Set where
  constructor autism-vaccine-current-sota-boundary
  field
    reviewExtendsThroughAugust2025 : Bool
    reviewExtendsThroughAugust2025IsTrue : reviewExtendsThroughAugust2025 ≡ true
    broaderVaccineASDNoCausalAssociationFindingReported : Bool
    broaderVaccineASDNoCausalAssociationFindingReportedIsTrue :
      broaderVaccineASDNoCausalAssociationFindingReported ≡ true
    broaderReviewAutomaticallyPaysExactHbombMMREstimand : Bool
    broaderReviewAutomaticallyPaysExactHbombMMREstimandIsFalse :
      broaderReviewAutomaticallyPaysExactHbombMMREstimand ≡ false
    sourceCitationCreatesAuthority : Bool
    sourceCitationCreatesAuthorityIsFalse : sourceCitationCreatesAuthority ≡ false
    reviewCreatesUniversalZeroRiskTheorem : Bool
    reviewCreatesUniversalZeroRiskTheoremIsFalse : reviewCreatesUniversalZeroRiskTheorem ≡ false
    reading : String

open AutismVaccineCurrentSOTABoundary public

canonicalAutismVaccineCurrentSOTABoundary : AutismVaccineCurrentSOTABoundary
canonicalAutismVaccineCurrentSOTABoundary =
  autism-vaccine-current-sota-boundary
    true refl
    true refl
    false refl
    false refl
    false refl
    "The September-2026 WHO review materially updates the surrounding evidence window and remains compatible with the bounded no-causal-association reading. It is still a distinct institutional/review-level source with a broader vaccine/ASD estimand; exact MMR claim payment continues to require its own typed scope match."
