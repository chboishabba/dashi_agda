module DASHI.Algebra.ClaimIndexedEvidencePolarityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _++_)

import DASHI.Algebra.DisagreementFourViewBoundary as Four

------------------------------------------------------------------------
-- Claim/context-indexed support-square pooling.
--
-- DASHI already represents evidence polarity as PolarAssessment =
-- (supports P, supports not-P).  The missing generic boundary is that pooling
-- is only well typed inside one common claim/context fibre.  Evidence about a
-- different claim, time, body, place, institution, observer, or provenance
-- scope must first cross an explicit alignment witness.
------------------------------------------------------------------------

infixl 5 _∨ᵇ_

_∨ᵇ_ : Bool → Bool → Bool
true  ∨ᵇ _ = true
false ∨ᵇ x = x

mergePolarity : Four.PolarAssessment → Four.PolarAssessment → Four.PolarAssessment
mergePolarity (Four.assess p n) (Four.assess p′ n′) =
  Four.assess (p ∨ᵇ p′) (n ∨ᵇ n′)

record ClaimFibreEvidence
    (Claim Context : Set)
    (claim : Claim)
    (context : Context) : Set where
  constructor claimFibreEvidence
  field
    polarity : Four.PolarAssessment
    provenance : List String

open ClaimFibreEvidence public

mergeSameFibre :
  ∀ {Claim Context claim context} →
  ClaimFibreEvidence Claim Context claim context →
  ClaimFibreEvidence Claim Context claim context →
  ClaimFibreEvidence Claim Context claim context
mergeSameFibre left right =
  claimFibreEvidence
    (mergePolarity (polarity left) (polarity right))
    (provenance left ++ provenance right)

mergeSameFibreSupports :
  ∀ {Claim Context claim context}
    (left right : ClaimFibreEvidence Claim Context claim context) →
  Four.supportsP (polarity (mergeSameFibre left right))
  ≡
  (Four.supportsP (polarity left) ∨ᵇ Four.supportsP (polarity right))
mergeSameFibreSupports (claimFibreEvidence (Four.assess p n) lp)
                       (claimFibreEvidence (Four.assess p′ n′) rp) = refl

mergeSameFibreRefutes :
  ∀ {Claim Context claim context}
    (left right : ClaimFibreEvidence Claim Context claim context) →
  Four.supportsNotP (polarity (mergeSameFibre left right))
  ≡
  (Four.supportsNotP (polarity left) ∨ᵇ Four.supportsNotP (polarity right))
mergeSameFibreRefutes (claimFibreEvidence (Four.assess p n) lp)
                      (claimFibreEvidence (Four.assess p′ n′) rp) = refl

------------------------------------------------------------------------
-- Cross-fibre pooling requires an explicit alignment witness.
------------------------------------------------------------------------

record EvidenceFibreAlignment
    {Claim Context : Set}
    (leftClaim rightClaim : Claim)
    (leftContext rightContext : Context) : Set where
  constructor evidenceFibreAlignment
  field
    claimAligned : leftClaim ≡ rightClaim
    contextAligned : leftContext ≡ rightContext

open EvidenceFibreAlignment public

transportEvidence :
  ∀ {Claim Context}
    {leftClaim rightClaim : Claim}
    {leftContext rightContext : Context} →
  leftClaim ≡ rightClaim →
  leftContext ≡ rightContext →
  ClaimFibreEvidence Claim Context leftClaim leftContext →
  ClaimFibreEvidence Claim Context rightClaim rightContext
transportEvidence refl refl evidence = evidence

mergeAlignedFibres :
  ∀ {Claim Context}
    {leftClaim rightClaim : Claim}
    {leftContext rightContext : Context} →
  ClaimFibreEvidence Claim Context leftClaim leftContext →
  ClaimFibreEvidence Claim Context rightClaim rightContext →
  EvidenceFibreAlignment leftClaim rightClaim leftContext rightContext →
  ClaimFibreEvidence Claim Context rightClaim rightContext
mergeAlignedFibres left right (evidenceFibreAlignment refl refl) =
  mergeSameFibre left right

------------------------------------------------------------------------
-- Canonical polarity witnesses.
------------------------------------------------------------------------

supportOnly : Four.PolarAssessment
supportOnly = Four.assess true false

refutationOnly : Four.PolarAssessment
refutationOnly = Four.assess false true

conflict : Four.PolarAssessment
conflict = mergePolarity supportOnly refutationOnly

ignorance : Four.PolarAssessment
ignorance = Four.assess false false

conflictIsBoth : conflict ≡ Four.assess true true
conflictIsBoth = refl

ignoranceIsNeither : ignorance ≡ Four.assess false false
ignoranceIsNeither = refl

record ClaimIndexedEvidencePolarityBoundary : Set where
  field
    poolingRequiresCommonTypedFibre : Bool
    crossFibrePoolingRequiresAlignment : Bool
    conflictRetainedBeforeProjection : Bool
    ignoranceRetainedBeforeProjection : Bool

canonicalClaimIndexedEvidencePolarityBoundary :
  ClaimIndexedEvidencePolarityBoundary
canonicalClaimIndexedEvidencePolarityBoundary = record
  { poolingRequiresCommonTypedFibre = true
  ; crossFibrePoolingRequiresAlignment = true
  ; conflictRetainedBeforeProjection = true
  ; ignoranceRetainedBeforeProjection = true
  }
