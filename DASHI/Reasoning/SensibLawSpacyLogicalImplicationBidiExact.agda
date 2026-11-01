module DASHI.Reasoning.SensibLawSpacyLogicalImplicationBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.SensibLawSpacyPredicateNormalFormBridgeExact as Bridge
import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as Candidate
import DASHI.Reasoning.PredicateNormalFormLogicalCalculusExact as Logic
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as EvidencePNF
open Candidate using (Formula; _⇒_)
open Logic using (_⊢_; formula; impElim; assumption; here; there)

------------------------------------------------------------------------
-- CAPSTONE: spaCy -> candidate semantics -> reviewed PNF -> logic -> cone
------------------------------------------------------------------------

record SpacyToLogicalImplicationRun
    (source : Cone.NaturalLanguageExperimentalAssertion) : Set₁ where
  constructor spacyToLogicalImplicationRun
  field
    numericReceipt : Bridge.SensibLawNumericPNFReceipt source

    semanticFibre : Candidate.CandidateSemanticFibre
    semanticResolution : Candidate.SemanticResolutionReceipt semanticFibre

    evidentialCompilation : Cone.PNFCompilationReceipt source
    parserToEvidence :
      Bridge.ParserToEvidencePNFCorrespondence
        numericReceipt evidentialCompilation

    candidateToEvidence :
      Candidate.ResolvedCandidateToEvidencePNF
        semanticResolution
        (Cone.compiled evidentialCompilation)

    logicalInterpretation :
      Logic.EvidencePNFLogicalInterpretation
        (Cone.compiled evidentialCompilation)

    derivedFormula : Formula
    logicalDerivation :
      formula logicalInterpretation ∷ [] ⊢ derivedFormula

    consequenceAuthority : Logic.ConsequenceAuthority
    consequenceAuthorityReference : String

    implicationCone : Cone.ExperimentalImplicationCone source
    coneLinkReference : String

open SpacyToLogicalImplicationRun public

record LogicalImplicationReadback
    {source : Cone.NaturalLanguageExperimentalAssertion}
    (run : SpacyToLogicalImplicationRun source) : Set₁ where
  constructor logicalImplicationReadback
  field
    parserRunReference : String
    semanticCandidateReference : String
    semanticResolutionReference : String
    evidentialPNFReference : String
    logicalFormulaReference : String
    implicationReference : String
    nonInvertibilityResidualReference : String

open LogicalImplicationReadback public

------------------------------------------------------------------------
-- Exact logical regressions.
------------------------------------------------------------------------

modusPonensFromTwoPremises :
  ∀ {φ ψ} →
  (φ ⇒ ψ) ∷ φ ∷ [] ⊢ ψ
modusPonensFromTwoPremises =
  impElim
    (assumption here)
    (assumption (there here))

causalPromotionStillNeedsEvidence :
  Logic.promotionAuthority EvidencePNF.strengthensCausalForce
  ≡ Logic.requiresAdditionalEmpiricalEvidence
causalPromotionStillNeedsEvidence = refl

transportStillNeedsEvidence :
  Logic.promotionAuthority EvidencePNF.widensPopulation
  ≡ Logic.requiresAdditionalEmpiricalEvidence
transportStillNeedsEvidence = refl

record SpacyLogicalImplicationBoundary : Set where
  constructor spacyLogicalImplicationBoundary
  field
    parserCandidateEqualsReviewedSemantics : Bool
    parserCandidateEqualsReviewedSemanticsIsFalse :
      parserCandidateEqualsReviewedSemantics ≡ false
    reviewedFormulaCanHaveLogicalConsequences : Bool
    reviewedFormulaCanHaveLogicalConsequencesIsTrue :
      reviewedFormulaCanHaveLogicalConsequences ≡ true
    logicalConsequenceAutomaticallySupportedConeEdge : Bool
    logicalConsequenceAutomaticallySupportedConeEdgeIsFalse :
      logicalConsequenceAutomaticallySupportedConeEdge ≡ false
    reverseTraceIsSemanticInverse : Bool
    reverseTraceIsSemanticInverseIsFalse :
      reverseTraceIsSemanticInverse ≡ false
    endToEndPathIsReceiptBearing : Bool
    endToEndPathIsReceiptBearingIsTrue :
      endToEndPathIsReceiptBearing ≡ true

canonicalSpacyLogicalImplicationBoundary : SpacyLogicalImplicationBoundary
canonicalSpacyLogicalImplicationBoundary =
  spacyLogicalImplicationBoundary false refl true refl false refl false refl true refl
