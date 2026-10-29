module DASHI.Cognition.PNF.RelationDeltaReconciliationRegression where

open import Agda.Builtin.Equality using (refl)
open import DASHI.Cognition.PNF.RelationDeltaReconciliationExact
import DASHI.Core.AuthorityNonPromotionCore as Authority
import DASHI.Interop.IntrospectiveProofLoopExact as Introspective

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


------------------------------------------------------------------------
-- ZKP O/R/C/S/L/P/G/F frame.
------------------------------------------------------------------------

candidateRelationZKPFrame : Introspective.ZKPFrame
candidateRelationZKPFrame =
  Introspective.zkp-frame
    "SensibLaw strict numeric PNF candidate reconciliation"
    "route all active candidate membership mutation through one desired/current reconciler"
    "migration 209 + RelationDeltaReconciliationExact + AffectedBoundaryLocalReductionExact"
    "affected parent demand keys, current candidate fibre, desired candidate fibre, reconciliation receipt"
    "RelationDeltaReceipt partition plus sparse affected-key lattice"
    "one mutation owner; unchanged rows retained; changed membership emits exact deltas"
    "same semantic authority with zero private bypass and zero manufactured unchanged transitions"
    "duplicate owner count + bypass count + unchanged rewrite count + missing hot-path reconciliation receipt"
