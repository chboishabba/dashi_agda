module DASHI.Reasoning.SpacyPNF369LogicalQualificationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as Spacy
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as Evidence
import DASHI.Reasoning.PredicateNormalFormLogicalCalculusExact as Logic
import DASHI.Reasoning.SpacyPNF369DialecticBridgeExact as Bridge369

------------------------------------------------------------------------
-- CAPSTONE: EXACT PARSER EVIDENCE + 369 REVIEW GEOMETRY + REVIEWED PNF + LOGIC
--
-- These coordinates travel together but retain different authority.
------------------------------------------------------------------------

record SpacyPNF369LogicalRun : Set₂ where
  constructor spacyPNF369LogicalRun
  field
    semanticFibre : Spacy.CandidateSemanticFibre
    resolution : Spacy.SemanticResolutionReceipt semanticFibre
    assertion : Evidence.PredicateNormalAssertion

    parserToPNF :
      Spacy.ResolvedCandidateToEvidencePNF resolution assertion

    dialectic369 : Bridge369.SpacyCandidateDialectic369Atom

    interpretation : Logic.EvidencePNFLogicalInterpretation assertion

    derivedFormula : Spacy.Formula
    logicalReadback :
      Logic.LogicalToEvidenceReadback interpretation derivedFormula

    parserHistoryReference : String
    dialecticReviewReference : String
    logicalDerivationReference : String

open SpacyPNF369LogicalRun public

------------------------------------------------------------------------
-- The actual parser evidence remains recoverable from the dialectic atom.
------------------------------------------------------------------------

leftParserWitness :
  SpacyPNF369LogicalRun → Spacy.DependencyWitness
leftParserWitness run =
  Spacy.forwardWitness (Bridge369.leftCandidate (dialectic369 run))

rightParserWitness :
  SpacyPNF369LogicalRun → Spacy.DependencyWitness
rightParserWitness run =
  Spacy.forwardWitness (Bridge369.rightCandidate (dialectic369 run))

------------------------------------------------------------------------
-- Object logic is independent of the 369 chart coordinate.
--
-- The chart can record review/dialectical position, but ordinary implication
-- elimination still consumes only actual logical derivations.
------------------------------------------------------------------------

modusPonensIgnores369Chart :
  ∀ {Γ φ ψ} →
  Bridge369.SpacyCandidateDialectic369Atom →
  Γ Logic.⊢ (φ Spacy.⇒ ψ) →
  Γ Logic.⊢ φ →
  Γ Logic.⊢ ψ
modusPonensIgnores369Chart chart implication premise =
  Logic.modusPonens implication premise

------------------------------------------------------------------------
-- Likewise, empirical-strength promotion remains controlled by the existing
-- PNF evidence delta, not by where the assertion sits in a 369 chart.
------------------------------------------------------------------------

promotionAuthorityIgnores369Chart :
  Bridge369.SpacyCandidateDialectic369Atom →
  (delta : Evidence.PromotionDelta) →
  Logic.ConsequenceAuthority
promotionAuthorityIgnores369Chart chart delta = Logic.promotionAuthority delta

causalStrengtheningStillNeedsEvidenceUnder369 :
  (chart : Bridge369.SpacyCandidateDialectic369Atom) →
  promotionAuthorityIgnores369Chart chart Evidence.strengthensCausalForce
  ≡ Logic.requiresAdditionalEmpiricalEvidence
causalStrengtheningStillNeedsEvidenceUnder369 chart = refl

populationWideningStillNeedsEvidenceUnder369 :
  (chart : Bridge369.SpacyCandidateDialectic369Atom) →
  promotionAuthorityIgnores369Chart chart Evidence.widensPopulation
  ≡ Logic.requiresAdditionalEmpiricalEvidence
populationWideningStillNeedsEvidenceUnder369 chart = refl

------------------------------------------------------------------------
-- Hard boundary.
------------------------------------------------------------------------

record SpacyPNF369LogicalBoundary : Set where
  constructor spacyPNF369LogicalBoundary
  field
    oneRunCanRetainParser369PNFAndLogic : Bool
    oneRunCanRetainParser369PNFAndLogicIsTrue :
      oneRunCanRetainParser369PNFAndLogic ≡ true

    chartCoordinateChangesObjectLogicRule : Bool
    chartCoordinateChangesObjectLogicRuleIsFalse :
      chartCoordinateChangesObjectLogicRule ≡ false

    highTritCreatesEmpiricalSupport : Bool
    highTritCreatesEmpiricalSupportIsFalse :
      highTritCreatesEmpiricalSupport ≡ false

    midTritRefutesFormula : Bool
    midTritRefutesFormulaIsFalse : midTritRefutesFormula ≡ false

    parserCandidateBecomesReviewedPNFWithoutReceipt : Bool
    parserCandidateBecomesReviewedPNFWithoutReceiptIsFalse :
      parserCandidateBecomesReviewedPNFWithoutReceipt ≡ false

    logicalDerivationReconstructsUniqueParserHistory : Bool
    logicalDerivationReconstructsUniqueParserHistoryIsFalse :
      logicalDerivationReconstructsUniqueParserHistory ≡ false

canonicalSpacyPNF369LogicalBoundary : SpacyPNF369LogicalBoundary
canonicalSpacyPNF369LogicalBoundary =
  spacyPNF369LogicalBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
