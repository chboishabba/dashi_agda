module DASHI.Cognition.PNF.SensibLawUnifiedPNFIntakeReentrySpineExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List)

import DASHI.Cognition.PNF.EventAlgebra as PNF

------------------------------------------------------------------------
-- M12 / Mary-rejoin: one semantic membrane for initial intake and
-- research re-entry.
--
-- literal source
--   -> source/revision/span-anchored statement
--   -> PNF candidate
--   -> parse review
--   -> later semantic admission
--
-- This owner deliberately stops before semantic admission.  A parse review
-- can make a candidate ready for admission review, but it cannot pay world
-- truth, proposition support, legal applicability, or legal authority.
------------------------------------------------------------------------

data StatementOrigin : Set where
  initialIntake researchReentry : StatementOrigin

record SourceStatementEnvelope : Set where
  constructor source-statement-envelope
  field
    statementRef : String
    documentRef : String
    sourceRevisionRef : String
    exactSpanRef : String
    literalText : String
    origin : StatementOrigin
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse : applicabilityPromoted ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false

open SourceStatementEnvelope public

record StatementCandidatePNF (statement : SourceStatementEnvelope) : Set where
  constructor statement-candidate-pnf
  field
    candidate : PNF.CandidatePNF
    parserReceiptRef : String
    candidateStillOnly : PNF.CandidatePNF.candidateOnly candidate ≡ true
    semanticAdmissionPaid : Bool
    semanticAdmissionDeferred : semanticAdmissionPaid ≡ false
    propositionSupportPaid : Bool
    propositionSupportDeferred : propositionSupportPaid ≡ false
    applicabilityPaid : Bool
    applicabilityDeferred : applicabilityPaid ≡ false
    claimTruthPaid : Bool
    claimTruthDeferred : claimTruthPaid ≡ false

open StatementCandidatePNF public

compileStatementPNF :
  (statement : SourceStatementEnvelope) →
  PNF.CandidatePNF →
  String →
  StatementCandidatePNF statement
compileStatementPNF statement candidate parserReceipt =
  statement-candidate-pnf
    candidate
    parserReceipt
    (PNF.CandidatePNF.candidateOnlyIsTrue candidate)
    false refl
    false refl
    false refl
    false refl

compileInitialIntake :
  (statement : SourceStatementEnvelope) →
  origin statement ≡ initialIntake →
  PNF.CandidatePNF →
  String →
  StatementCandidatePNF statement
compileInitialIntake statement refl candidate parserReceipt =
  compileStatementPNF statement candidate parserReceipt

compileResearchReentry :
  (statement : SourceStatementEnvelope) →
  origin statement ≡ researchReentry →
  PNF.CandidatePNF →
  String →
  StatementCandidatePNF statement
compileResearchReentry statement refl candidate parserReceipt =
  compileStatementPNF statement candidate parserReceipt

------------------------------------------------------------------------
-- Both doors use the same PNF compiler: origin affects provenance/workflow,
-- not the semantic meaning of an otherwise identical candidate.
------------------------------------------------------------------------

initialCompilerCandidateIsInput :
  ∀ {statement originProof candidate parserReceipt} →
  StatementCandidatePNF.candidate
    (compileInitialIntake statement originProof candidate parserReceipt)
  ≡ candidate
initialCompilerCandidateIsInput = refl

reentryCompilerCandidateIsInput :
  ∀ {statement originProof candidate parserReceipt} →
  StatementCandidatePNF.candidate
    (compileResearchReentry statement originProof candidate parserReceipt)
  ≡ candidate
reentryCompilerCandidateIsInput = refl

data ParseReviewDisposition : Set where
  acceptedForAdmissionReview rejected abstained qualified :
    ParseReviewDisposition

record StatementParseReview
    {statement : SourceStatementEnvelope}
    (parsed : StatementCandidatePNF statement) : Set where
  constructor statement-parse-review
  field
    reviewRef : String
    disposition : ParseReviewDisposition
    qualificationRef : String
    reviewedCandidate : PNF.CandidatePNF
    sameCandidate :
      reviewedCandidate ≡ StatementCandidatePNF.candidate parsed

open StatementParseReview public

record ReviewedStatementPNF
    {statement : SourceStatementEnvelope}
    (parsed : StatementCandidatePNF statement) : Set where
  constructor reviewed-statement-pnf
  field
    reviews : List (StatementParseReview parsed)
    semanticAdmissionPaid : Bool
    semanticAdmissionDeferred : semanticAdmissionPaid ≡ false
    propositionSupportPaid : Bool
    propositionSupportDeferred : propositionSupportPaid ≡ false
    applicabilityPaid : Bool
    applicabilityDeferred : applicabilityPaid ≡ false
    claimTruthPaid : Bool
    claimTruthDeferred : claimTruthPaid ≡ false

open ReviewedStatementPNF public

reviewStatementPNF :
  ∀ {statement} →
  (parsed : StatementCandidatePNF statement) →
  List (StatementParseReview parsed) →
  ReviewedStatementPNF parsed
reviewStatementPNF parsed reviews =
  reviewed-statement-pnf
    reviews
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Firewalls: these are different typed transitions.
------------------------------------------------------------------------

data ParserOutputIsWorldFact : Set where
data ParseReviewIsSemanticAdmission : Set where
data ParseReviewPaysPropositionSupport : Set where
data ParseReviewPaysLegalApplicability : Set where
data ParseReviewPaysClaimTruth : Set where
data ResearchReentryMayBypassCandidateReview : Set where

parserOutputDoesNotBecomeWorldFact : ParserOutputIsWorldFact → ⊥
parserOutputDoesNotBecomeWorldFact ()

parseReviewDoesNotBecomeSemanticAdmission :
  ParseReviewIsSemanticAdmission → ⊥
parseReviewDoesNotBecomeSemanticAdmission ()

parseReviewDoesNotPayPropositionSupport :
  ParseReviewPaysPropositionSupport → ⊥
parseReviewDoesNotPayPropositionSupport ()

parseReviewDoesNotPayLegalApplicability :
  ParseReviewPaysLegalApplicability → ⊥
parseReviewDoesNotPayLegalApplicability ()

parseReviewDoesNotPayClaimTruth :
  ParseReviewPaysClaimTruth → ⊥
parseReviewDoesNotPayClaimTruth ()

researchReentryCannotBypassCandidateReview :
  ResearchReentryMayBypassCandidateReview → ⊥
researchReentryCannotBypassCandidateReview ()

record UnifiedPNFIntakeReentryBoundary : Set where
  constructor unified-pnf-intake-reentry-boundary
  field
    sourceRevisionRetained : Bool
    exactSpanRetained : Bool
    statementLayerExplicit : Bool
    oneCompilerForInitialAndReentry : Bool
    parserDirectlyPromotesWorldFact : Bool
    parseReviewPaysSemanticAdmission : Bool

canonicalUnifiedPNFIntakeReentryBoundary :
  UnifiedPNFIntakeReentryBoundary
canonicalUnifiedPNFIntakeReentryBoundary =
  unified-pnf-intake-reentry-boundary
    true true true true false false
