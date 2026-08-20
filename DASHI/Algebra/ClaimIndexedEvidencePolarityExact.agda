module DASHI.Algebra.ClaimIndexedEvidencePolarityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _++_)

import DASHI.Algebra.DisagreementFourViewBoundary as Four
import DASHI.Reasoning.RelationalLensSynthesisCore as Lens

------------------------------------------------------------------------
-- Claim/context/operator-indexed support-square pooling.
--
-- DASHI already represents a two-coordinate information carrier as
-- PolarAssessment. IMPORTANT: the second Boolean coordinate is NOT treated
-- here as automatically meaning classical/logical negation of the first claim.
-- Existing DASHI foundations distinguish logical negation, algebraic inverse,
-- orientation reversal, contextual counterposition and lens transition.
--
-- Logical/informational calibration:
-- Nuel D. Belnap, "A Useful Four-Valued Logic" (1977),
-- DOI 10.1007/978-94-010-1161-7_2.
-- J. Michael Dunn, "Intuitive Semantics for First-Degree Entailments and
-- 'Coupled Trees'" (1976), DOI 10.1007/BF00373152.
------------------------------------------------------------------------

infixl 5 _∨ᵇ_
_∨ᵇ_ : Bool → Bool → Bool
true ∨ᵇ _ = true
false ∨ᵇ x = x

mergePolarity : Four.PolarAssessment → Four.PolarAssessment → Four.PolarAssessment
mergePolarity (Four.assess p n) (Four.assess p′ n′) = Four.assess (p ∨ᵇ p′) (n ∨ᵇ n′)

record OppositionDescriptor (Claim : Set) : Set where
  constructor oppositionDescriptor
  field
    baseClaim : Claim
    opposingClaim : Claim
    operatorRole : Lens.RelationalOperatorRole
    applyOperator : Claim → Claim
    opposingClaimExact : applyOperator baseClaim ≡ opposingClaim
open OppositionDescriptor public

record LogicalNegationQualified {Claim : Set} (opposition : OppositionDescriptor Claim) : Set where
  constructor logicalNegationQualified
  field
    roleIsLogicalNegation : operatorRole opposition ≡ Lens.logicalNegationRole
open LogicalNegationQualified public

contextualCounterpositionRoleIsNotLogicalNegation :
  Lens.contextualCounterpositionRole ≡ Lens.logicalNegationRole → ⊥
contextualCounterpositionRoleIsNotLogicalNegation = Lens.contextualCounterpositionIsNotLogicalNegationByRole

orientationReversalRoleIsNotLogicalNegation :
  Lens.orientationReversalRole ≡ Lens.logicalNegationRole → ⊥
orientationReversalRoleIsNotLogicalNegation = Lens.orientationReversalIsNotLogicalNegation

record ClaimFibreEvidence (Claim Context : Set) (opposition : OppositionDescriptor Claim) (context : Context) : Set where
  constructor claimFibreEvidence
  field
    polarity : Four.PolarAssessment
    provenance : List String
open ClaimFibreEvidence public

supportsBaseClaim : ∀ {Claim Context opposition context} → ClaimFibreEvidence Claim Context opposition context → Bool
supportsBaseClaim evidence = Four.supportsP (polarity evidence)

supportsOpposingClaim : ∀ {Claim Context opposition context} → ClaimFibreEvidence Claim Context opposition context → Bool
supportsOpposingClaim evidence = Four.supportsNotP (polarity evidence)

supportsLogicalNegation : ∀ {Claim Context opposition context} → LogicalNegationQualified opposition → ClaimFibreEvidence Claim Context opposition context → Bool
supportsLogicalNegation qualification evidence = supportsOpposingClaim evidence

mergeSameFibre : ∀ {Claim Context opposition context} → ClaimFibreEvidence Claim Context opposition context → ClaimFibreEvidence Claim Context opposition context → ClaimFibreEvidence Claim Context opposition context
mergeSameFibre left right = claimFibreEvidence (mergePolarity (polarity left) (polarity right)) (provenance left ++ provenance right)

mergeSameFibreSupportsBase : ∀ {Claim Context opposition context} (left right : ClaimFibreEvidence Claim Context opposition context) → supportsBaseClaim (mergeSameFibre left right) ≡ (supportsBaseClaim left ∨ᵇ supportsBaseClaim right)
mergeSameFibreSupportsBase (claimFibreEvidence (Four.assess p n) lp) (claimFibreEvidence (Four.assess p′ n′) rp) = refl

mergeSameFibreSupportsOpposing : ∀ {Claim Context opposition context} (left right : ClaimFibreEvidence Claim Context opposition context) → supportsOpposingClaim (mergeSameFibre left right) ≡ (supportsOpposingClaim left ∨ᵇ supportsOpposingClaim right)
mergeSameFibreSupportsOpposing (claimFibreEvidence (Four.assess p n) lp) (claimFibreEvidence (Four.assess p′ n′) rp) = refl

record EvidenceFibreAlignment {Claim Context : Set}
    (leftOpposition rightOpposition : OppositionDescriptor Claim)
    (leftContext rightContext : Context) : Set where
  constructor evidenceFibreAlignment
  field
    oppositionAligned : leftOpposition ≡ rightOpposition
    contextAligned : leftContext ≡ rightContext
open EvidenceFibreAlignment public

transportEvidence : ∀ {Claim Context} {leftOpposition rightOpposition : OppositionDescriptor Claim} {leftContext rightContext : Context} → leftOpposition ≡ rightOpposition → leftContext ≡ rightContext → ClaimFibreEvidence Claim Context leftOpposition leftContext → ClaimFibreEvidence Claim Context rightOpposition rightContext
transportEvidence refl refl evidence = evidence

mergeAlignedFibres : ∀ {Claim Context} {leftOpposition rightOpposition : OppositionDescriptor Claim} {leftContext rightContext : Context} → ClaimFibreEvidence Claim Context leftOpposition leftContext → ClaimFibreEvidence Claim Context rightOpposition rightContext → EvidenceFibreAlignment leftOpposition rightOpposition leftContext rightContext → ClaimFibreEvidence Claim Context rightOpposition rightContext
mergeAlignedFibres left right (evidenceFibreAlignment refl refl) = mergeSameFibre left right

supportOnly : Four.PolarAssessment
supportOnly = Four.assess true false
opposingSupportOnly : Four.PolarAssessment
opposingSupportOnly = Four.assess false true
conflict : Four.PolarAssessment
conflict = mergePolarity supportOnly opposingSupportOnly
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
    oppositionRoleExplicit : Bool
    opposingSupportAutomaticallyMeansLogicalNegation : Bool
    inversionReversalCounterpositionNegationCollapsed : Bool
    conflictRetainedBeforeProjection : Bool
    ignoranceRetainedBeforeProjection : Bool

canonicalClaimIndexedEvidencePolarityBoundary : ClaimIndexedEvidencePolarityBoundary
canonicalClaimIndexedEvidencePolarityBoundary = record
  { poolingRequiresCommonTypedFibre = true
  ; crossFibrePoolingRequiresAlignment = true
  ; oppositionRoleExplicit = true
  ; opposingSupportAutomaticallyMeansLogicalNegation = false
  ; inversionReversalCounterpositionNegationCollapsed = false
  ; conflictRetainedBeforeProjection = true
  ; ignoranceRetainedBeforeProjection = true
  }
