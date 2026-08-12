module DASHI.Cognition.PNF.EvidenceCoverageAudit where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Cognition.PNF.ComplexityArithmetic
import DASHI.Cognition.PNF.SparseFibredFrontier as Sparse

------------------------------------------------------------------------
-- Empirical coverage receipts for the numeric PNF acceptance corpus.
--
-- These records do not infer semantic truth from counts.  They make the
-- diagnostic funnels explicit so runtime reports can instantiate the same
-- shape that the architecture reasons about.
------------------------------------------------------------------------

data StructuralLevel : Set where
  sentenceLevel paragraphLevel adaptiveLevel documentLevel : StructuralLevel

record IdentityFactorCoverageCell (level : StructuralLevel) : Set where
  constructor identityFactorCoverageCell
  field
    identityBearingCount : Nat
    factorBearingCount : Nat
    identityFactorIntersectionCount : Nat
    intersectionWithinIdentity :
      identityFactorIntersectionCount ≤ᶜ identityBearingCount
    intersectionWithinFactors :
      identityFactorIntersectionCount ≤ᶜ factorBearingCount

open IdentityFactorCoverageCell public

record FrontierCoverageReceipt : Set where
  constructor frontierCoverageReceipt
  field
    sparseReduction : Sparse.SparseFrontierCertificate
    sentenceCoverage : IdentityFactorCoverageCell sentenceLevel
    paragraphCoverage : IdentityFactorCoverageCell paragraphLevel
    adaptiveCoverage : IdentityFactorCoverageCell adaptiveLevel
    documentCoverage : IdentityFactorCoverageCell documentLevel

open FrontierCoverageReceipt public

------------------------------------------------------------------------
-- Typed-demand / anaphor funnel.
--
-- Zero source proofs can arise at several distinct stages.  Runtime diagnostics
-- should therefore report the whole monotone funnel rather than only its last
-- number.
------------------------------------------------------------------------

record TypedDemandResolutionFunnel : Set where
  constructor typedDemandResolutionFunnel
  field
    generatedDemandCount : Nat
    demandWithCandidateCount : Nat
    uniqueCandidateDemandCount : Nat
    admittedIdentityWitnessCount : Nat
    factorSubstitutionCount : Nat
    candidateStageWithinGenerated :
      demandWithCandidateCount ≤ᶜ generatedDemandCount
    uniqueStageWithinCandidateStage :
      uniqueCandidateDemandCount ≤ᶜ demandWithCandidateCount
    admittedStageWithinUniqueStage :
      admittedIdentityWitnessCount ≤ᶜ uniqueCandidateDemandCount
    factorStageWithinAdmittedStage :
      factorSubstitutionCount ≤ᶜ admittedIdentityWitnessCount

open TypedDemandResolutionFunnel public

------------------------------------------------------------------------
-- Proof multiplicity versus proposition coverage.
--
-- Independent witnesses for one source/target proposition are useful evidence,
-- but witness-row count must not be mistaken for distinct identity coverage.
------------------------------------------------------------------------

record IdentityProofMultiplicityReceipt : Set where
  constructor identityProofMultiplicityReceipt
  field
    admittedWitnessRowCount : Nat
    distinctSourceTargetPropositionCount : Nat
    distinctPropositionsWithinWitnessRows :
      distinctSourceTargetPropositionCount ≤ᶜ admittedWitnessRowCount

open IdentityProofMultiplicityReceipt public

record EvidenceCoverageAudit : Set where
  constructor evidenceCoverageAudit
  field
    frontierCoverage : FrontierCoverageReceipt
    typedDemandFunnel : TypedDemandResolutionFunnel
    proofMultiplicity : IdentityProofMultiplicityReceipt

open EvidenceCoverageAudit public

record EvidenceCoverageAuditBoundary : Set where
  constructor evidenceCoverageAuditBoundary
  field
    countsPromoteSemanticTruth : Bool
    countsPromoteSemanticTruthIsFalse : countsPromoteSemanticTruth ≡ false
    lowCoverageInvalidatesAnOtherwiseValidIdentityProof : Bool
    lowCoverageInvalidatesAnOtherwiseValidIdentityProofIsFalse :
      lowCoverageInvalidatesAnOtherwiseValidIdentityProof ≡ false
    zeroFinalDemandYieldIdentifiesFailureStageWithoutFunnel : Bool
    zeroFinalDemandYieldIdentifiesFailureStageWithoutFunnelIsFalse :
      zeroFinalDemandYieldIdentifiesFailureStageWithoutFunnel ≡ false

open EvidenceCoverageAuditBoundary public

canonicalEvidenceCoverageAuditBoundary : EvidenceCoverageAuditBoundary
canonicalEvidenceCoverageAuditBoundary =
  evidenceCoverageAuditBoundary
    false refl
    false refl
    false refl
