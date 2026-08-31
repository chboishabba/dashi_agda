module DASHI.Reasoning.PredicateNormalFormLogicalCalculusExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as Candidate
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as EvidencePNF
open Candidate using (Formula; Term; _∧_; _∨_; _⇒_)

infix 4 _∈_
data _∈_ {A : Set} (x : A) : List A → Set where
  here : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

------------------------------------------------------------------------
-- OBJECT LOGIC OVER REVIEWED PNF FORMULAE
------------------------------------------------------------------------

infix 3 _⊢_
data _⊢_ : List Formula → Formula → Set where
  assumption : ∀ {Γ φ} → φ ∈ Γ → Γ ⊢ φ
  andIntro : ∀ {Γ φ ψ} → Γ ⊢ φ → Γ ⊢ ψ → Γ ⊢ (φ ∧ ψ)
  andElimL : ∀ {Γ φ ψ} → Γ ⊢ (φ ∧ ψ) → Γ ⊢ φ
  andElimR : ∀ {Γ φ ψ} → Γ ⊢ (φ ∧ ψ) → Γ ⊢ ψ
  impIntro : ∀ {Γ φ ψ} → (φ ∷ Γ) ⊢ ψ → Γ ⊢ (φ ⇒ ψ)
  impElim : ∀ {Γ φ ψ} → Γ ⊢ (φ ⇒ ψ) → Γ ⊢ φ → Γ ⊢ ψ
  orIntroL : ∀ {Γ φ ψ} → Γ ⊢ φ → Γ ⊢ (φ ∨ ψ)
  orIntroR : ∀ {Γ φ ψ} → Γ ⊢ ψ → Γ ⊢ (φ ∨ ψ)

record EvidencePNFLogicalInterpretation
    (assertion : EvidencePNF.PredicateNormalAssertion) : Set₁ where
  constructor evidencePNFLogicalInterpretation
  field
    formula : Formula
    predicateInterpretationReference : String
    quantifierInterpretationReference : String
    scopeInterpretationReference : String
    inferentialForceInterpretationReference : String
    interpretationReviewReference : String

open EvidencePNFLogicalInterpretation public

record LogicalToEvidenceReadback
    {assertion : EvidencePNF.PredicateNormalAssertion}
    (interpretation : EvidencePNFLogicalInterpretation assertion)
    (derived : Formula) : Set₁ where
  constructor logicalToEvidenceReadback
  field
    derivation : formula interpretation ∷ [] ⊢ derived
    readingReference : String
    sameEmpiricalScopeReference : String
    noStrengtheningReference : String

open LogicalToEvidenceReadback public

data ConsequenceAuthority : Set where
  purelyLogicalConsequence
  requiresAdditionalEmpiricalEvidence
  blockedByMissingEvidence
  : ConsequenceAuthority

record EvidenceQualifiedConsequence : Set₁ where
  constructor evidenceQualifiedConsequence
  field
    sourceAssertion : EvidencePNF.PredicateNormalAssertion
    sourceInterpretation : EvidencePNFLogicalInterpretation sourceAssertion
    consequence : Formula
    logicalDerivationReference : String
    authority : ConsequenceAuthority
    empiricalPromotionReference : String

open EvidenceQualifiedConsequence public

promotionAuthority : EvidencePNF.PromotionDelta → ConsequenceAuthority
promotionAuthority EvidencePNF.sameAssertionStrength = purelyLogicalConsequence
promotionAuthority EvidencePNF.widensPopulation = requiresAdditionalEmpiricalEvidence
promotionAuthority EvidencePNF.widensContext = requiresAdditionalEmpiricalEvidence
promotionAuthority EvidencePNF.strengthensQuantifier = requiresAdditionalEmpiricalEvidence
promotionAuthority EvidencePNF.strengthensCausalForce = requiresAdditionalEmpiricalEvidence
promotionAuthority EvidencePNF.strengthensComparativeForce = requiresAdditionalEmpiricalEvidence
promotionAuthority EvidencePNF.strengthensNormativeForce = requiresAdditionalEmpiricalEvidence
promotionAuthority EvidencePNF.dropsContextPredicate = requiresAdditionalEmpiricalEvidence
promotionAuthority EvidencePNF.dropsComparator = requiresAdditionalEmpiricalEvidence
promotionAuthority EvidencePNF.dropsUncertainty = requiresAdditionalEmpiricalEvidence

causalStrengtheningNotPureLogic :
  promotionAuthority EvidencePNF.strengthensCausalForce
  ≡ requiresAdditionalEmpiricalEvidence
causalStrengtheningNotPureLogic = refl

populationWideningNotPureLogic :
  promotionAuthority EvidencePNF.widensPopulation
  ≡ requiresAdditionalEmpiricalEvidence
populationWideningNotPureLogic = refl

modusPonens : ∀ {Γ φ ψ} → Γ ⊢ (φ ⇒ ψ) → Γ ⊢ φ → Γ ⊢ ψ
modusPonens = impElim

record PNFLogicalBoundary : Set where
  constructor pnfLogicalBoundary
  field
    logicalEntailmentEqualsEmpiricalSupport : Bool
    logicalEntailmentEqualsEmpiricalSupportIsFalse :
      logicalEntailmentEqualsEmpiricalSupport ≡ false
    modusPonensRequiresNewEmpiricalEvidence : Bool
    modusPonensRequiresNewEmpiricalEvidenceIsFalse :
      modusPonensRequiresNewEmpiricalEvidence ≡ false
    causalPromotionCanBeObtainedBySyntaxAlone : Bool
    causalPromotionCanBeObtainedBySyntaxAloneIsFalse :
      causalPromotionCanBeObtainedBySyntaxAlone ≡ false
    transportCanBeObtainedBySyntaxAlone : Bool
    transportCanBeObtainedBySyntaxAloneIsFalse :
      transportCanBeObtainedBySyntaxAlone ≡ false
    logicalReadbackIsReceiptBearing : Bool
    logicalReadbackIsReceiptBearingIsTrue :
      logicalReadbackIsReceiptBearing ≡ true

canonicalPNFLogicalBoundary : PNFLogicalBoundary
canonicalPNFLogicalBoundary =
  pnfLogicalBoundary false refl false refl false refl false refl true refl
