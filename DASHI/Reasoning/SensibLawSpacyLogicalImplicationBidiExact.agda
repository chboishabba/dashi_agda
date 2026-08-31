module DASHI.Reasoning.SensibLawSpacyLogicalImplicationBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.SensibLawSpacyPredicateNormalFormBridgeExact as Bridge
import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as Candidate
import DASHI.Reasoning.PredicateNormalFormLogicalCalculusExact as Logic
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as EvidencePNF

------------------------------------------------------------------------
-- CAPSTONE: spaCy -> candidate semantics -> reviewed PNF -> logic -> cone
--
-- Every arrow is receipt-bearing and the reverse direction remains visible:
-- a logical reading retains the semantic candidate/resolution that supported
-- it, and that candidate retains the parser dependency observation that
-- proposed it.  Logical closure is not silently promoted to empirical support.
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

    derivedFormula : Candidate.Formula
    logicalDerivation :
      Logic.formula logicalInterpretation ∷ [] Logic.⊢ derivedFormula

    consequenceAuthority : Logic.ConsequenceAuthority
    consequenceAuthorityReference : String

    implicationCone : Cone.ExperimentalImplicationCone source
    coneLinkReference : String

open SpacyToLogicalImplicationRun public

------------------------------------------------------------------------
-- The BIDI readback exposes both ends of the path without claiming inverse
-- equivalence.  We can trace a consequence back to its reviewed assertion and
-- parser-supported semantic candidate, but many parser surfaces/readings may
-- inhabit the same logical formula and one parse may support several readings.
------------------------------------------------------------------------

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
  (φ Candidate.⇒ ψ) ∷ φ ∷ [] Logic.⊢ ψ
modusPonensFromTwoPremises =
  Logic.impElim
    (Logic.assumption Logic.here)
    (Logic.assumption (Logic.there Logic.here))

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
  spacyLogicalImplicationBoundary
    false refl
    true refl
    false refl
    false refl
    true refl
