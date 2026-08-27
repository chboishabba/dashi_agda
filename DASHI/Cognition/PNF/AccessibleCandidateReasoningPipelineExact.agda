module DASHI.Cognition.PNF.AccessibleCandidateReasoningPipelineExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Reasoning.FallacyObstructionCatalogue as Fallacy

------------------------------------------------------------------------
-- Pre-decision architecture only:
--
-- stored candidate -> current access -> argument audit -> action reachability.
--
-- No generic selection/utility/DecisionTheory is introduced.  Existing Pareto
-- and branch/attractor owners may consume this surface downstream.
------------------------------------------------------------------------

data Candidate : Set where
  supportingCandidate counterCandidate : Candidate

data AccessMode : Set where
  narrowedAccess broadenedAccess : AccessMode

data AuditStatus : Set where
  cleanAudit : AuditStatus
  obstructedAudit : Fallacy.FallacyObstruction → AuditStatus

stored : Candidate → Bool
stored _ = true

accessible : AccessMode → Candidate → Bool
accessible narrowedAccess supportingCandidate = true
accessible narrowedAccess counterCandidate = false
accessible broadenedAccess supportingCandidate = true
accessible broadenedAccess counterCandidate = true

auditPasses : AuditStatus → Bool
auditPasses cleanAudit = true
auditPasses (obstructedAudit _) = false

boolAnd : Bool → Bool → Bool
boolAnd true b = b
boolAnd false _ = false

actionable : AccessMode → Candidate → AuditStatus → Bool
actionable mode candidate audit =
  boolAnd (accessible mode candidate) (auditPasses audit)

counterStoredUnderEitherMode :
  stored counterCandidate ≡ true
counterStoredUnderEitherMode = refl

counterNotAccessibleWhenNarrowed :
  accessible narrowedAccess counterCandidate ≡ false
counterNotAccessibleWhenNarrowed = refl

counterAccessibleWhenBroadened :
  accessible broadenedAccess counterCandidate ≡ true
counterAccessibleWhenBroadened = refl

sameStoredCandidateDifferentLiveSurface :
  accessible narrowedAccess counterCandidate
  ≡ accessible broadenedAccess counterCandidate → ⊥
sameStoredCandidateDifferentLiveSurface ()

accessDoesNotBypassFallacyAudit :
  actionable broadenedAccess counterCandidate
    (obstructedAudit Fallacy.missingPremiseSupport)
  ≡ false
accessDoesNotBypassFallacyAudit = refl

accessibleCleanCandidateBecomesActionable :
  actionable broadenedAccess counterCandidate cleanAudit ≡ true
accessibleCleanCandidateBecomesActionable = refl

sameAccessibilityDifferentAuditOutcome :
  actionable broadenedAccess counterCandidate cleanAudit
  ≡
  actionable broadenedAccess counterCandidate
    (obstructedAudit Fallacy.semanticEquivocation) → ⊥
sameAccessibilityDifferentAuditOutcome ()

record PreDecisionPipelineBoundary : Set where
  constructor preDecisionPipelineBoundary
  field
    storedMeansAccessible : Bool
    accessibleMeansAuditClean : Bool
    auditCleanMeansActionRequired : Bool
    selectionOperatorProvided : Bool
    accessExpansionChangesStoredCarrier : Bool

canonicalPreDecisionPipelineBoundary : PreDecisionPipelineBoundary
canonicalPreDecisionPipelineBoundary =
  preDecisionPipelineBoundary false false false false false
