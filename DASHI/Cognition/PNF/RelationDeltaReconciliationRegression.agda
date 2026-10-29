module DASHI.Cognition.PNF.RelationDeltaReconciliationRegression where

open import Agda.Builtin.Equality using (refl)
open import DASHI.Cognition.PNF.RelationDeltaReconciliationExact
import DASHI.Core.AuthorityNonPromotionCore as Authority

oneAddOneRemoveOneReplaceOneSkip : RelationDeltaReceipt
oneAddOneRemoveOneReplaceOneSkip =
  relationDeltaReceipt
    3
    3
    1
    1
    1
    1
    4
    refl
    refl
    refl

transitionBoundary : RelationDeltaTransitionBoundary
transitionBoundary =
  relationDeltaTransitionBoundary
    oneAddOneRemoveOneReplaceOneSkip
    4
    refl

------------------------------------------------------------------------
-- SensibLaw C3d routing witness.
------------------------------------------------------------------------

singleCandidateRelationOwner : RelationDeltaOwnerRouting
singleCandidateRelationOwner =
  relationDeltaOwnerRouting
    1
    0
    1
    1
    refl
    refl
    refl
    refl


candidateRelationExecutionBoundary : RelationDeltaAuthorityBoundary
candidateRelationExecutionBoundary =
  relationDeltaAuthorityBoundary
    singleCandidateRelationOwner
    (Authority.mkClosedAuthorityNonPromotionBundle
      "sensiblaw-relation-delta-execution-owner")
