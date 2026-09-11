module DASHI.Cognition.PNF.SensibLawDiscourseQualityAuditExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawBroadcastDiscourseSpanReconstructionExact as Spans
import DASHI.Cognition.PNF.SensibLawRoleTransitionManifoldExact as Roles

------------------------------------------------------------------------
-- Discourse-specific quality audit.
--
-- Global PNF residual count is too coarse to evaluate transcript reconstruction.
-- Keep attribution ambiguity, speaker ambiguity, clause-attribution ambiguity,
-- hidden-splice risk, false-cut risk, Pareto width, and scope-shift observations
-- as separate diagnostic coordinates.  World-model mismatch is intentionally
-- absent until a separate world-constraint receipt exists.
------------------------------------------------------------------------

record DiscourseQualitySummary : Set where
  constructor discourseQualitySummary
  field
    runtimeSchemaReference : String
    rankOneBoundaryCount : Nat
    unresolvedRankOneCount : Nat
    admittedHardCutCount : Nat
    typedRoleBlockedCount : Nat
    attributionAmbiguityCount : Nat
    speakerAmbiguityCount : Nat
    clauseAttributionAmbiguityCount : Nat
    hiddenSpeakerSpliceRiskCount : Nat
    falseCutRiskCount : Nat
    paretoWidthSum : Nat
    negationShiftCount : Nat
    modalityShiftCount : Nat
    worldMismatchObserved : Bool
    comparisonOnly : Bool
    candidateOnly : Bool

open DiscourseQualitySummary public

record BoundaryQualityObservation : Set where
  constructor boundaryQualityObservation
  field
    boundaryReference : String
    paretoReference : String
    roleTransitionReference : String
    hardCutAdmissionReference : String
    attributionAmbiguityReference : String
    speakerAmbiguityReference : String
    clauseAttributionReference : String
    hiddenSpliceRiskReference : String
    falseCutRiskReference : String
    scopeShiftReference : String
    worldMismatchReference : String

open BoundaryQualityObservation public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data LowerResidualMeansBetterDiscourse : Set where
lowerResidualDoesNotMeanBetterDiscourse : LowerResidualMeansBetterDiscourse → ⊥
lowerResidualDoesNotMeanBetterDiscourse ()

data HiddenSpliceRiskVerifiesSpeakerChange : Set where
hiddenSpliceRiskDoesNotVerifySpeakerChange : HiddenSpliceRiskVerifiesSpeakerChange → ⊥
hiddenSpliceRiskDoesNotVerifySpeakerChange ()

data AttributionAmbiguityMeansAttributionFalse : Set where
attributionAmbiguityDoesNotMeanAttributionFalse : AttributionAmbiguityMeansAttributionFalse → ⊥
attributionAmbiguityDoesNotMeanAttributionFalse ()

data MissingWorldReceiptMayBeCountedAsWorldMismatch : Set where
missingWorldReceiptMayNotBeCountedAsWorldMismatch : MissingWorldReceiptMayBeCountedAsWorldMismatch → ⊥
missingWorldReceiptMayNotBeCountedAsWorldMismatch ()

data QualityAuditPromotesPolicyClaim : Set where
qualityAuditDoesNotPromotePolicyClaim : QualityAuditPromotesPolicyClaim → ⊥
qualityAuditDoesNotPromotePolicyClaim ()

record DiscourseQualityBoundary : Set where
  constructor discourseQualityBoundary
  field
    globalResidualIsDiagnosticOnly : Bool
    attributionAndSpeakerAmbiguitySeparated : Bool
    hiddenSpliceAndFalseCutSeparated : Bool
    roleCompatibilityRetained : Bool
    worldMismatchRequiresSeparateReceipt : Bool
    qualityAuditMayPromotePolicyTruth : Bool

canonicalDiscourseQualityBoundary : DiscourseQualityBoundary
canonicalDiscourseQualityBoundary =
  discourseQualityBoundary true true true true true false

spanBoundaryAnchor : Spans.SpanReconstructionBoundary
spanBoundaryAnchor = Spans.canonicalSpanReconstructionBoundary

roleBoundaryAnchor : Roles.RoleTransitionBoundary
roleBoundaryAnchor = Roles.canonicalRoleTransitionBoundary
