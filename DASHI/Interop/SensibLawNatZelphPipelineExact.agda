module DASHI.Interop.SensibLawNatZelphPipelineExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.AristotleConservativeTypeModuleBoundaryExact as TypeModule
import DASHI.Interop.SensibLawWikibaseZelphItemSurfaceExact as Join
import DASHI.Interop.SensibLawNatZelphPeerCohortExact as Peer
import DASHI.Interop.SensibLawNatPeerPressureWeldExact as Weld
import DASHI.Interop.ZelphPrunedArtifactQueryPreservationExact as Preservation

------------------------------------------------------------------------
-- Runtime parity owner for:
--   src/policy/zelph_routed_relation_observations.py
--   src/policy/nat_zelph_peer_pipeline.py
--
-- ITIR bounded_graph_slice_plan is a transport plan, not a query result.  This
-- carrier begins only after an actual routed Zelph execution has emitted
-- explicit normalized P31/P279 relation observations.
------------------------------------------------------------------------

data RoutedTypeRelation : Set where
  routedP31 routedP279 : RoutedTypeRelation

record RoutedZelphRelationObservation : Set where
  constructor routed-zelph-relation-observation
  field
    sourceReference : String
    relation : RoutedTypeRelation
    objectReference : String
    executionReceiptReference : String
    graphViewReference : String
    graphRevisionReference : String
    queryFamilyReference : String
    nativeStatementAuthority : Bool
    nativeStatementAuthorityIsFalse : nativeStatementAuthority ≡ false
    truthAuthority : Bool
    truthAuthorityIsFalse : truthAuthority ≡ false
open RoutedZelphRelationObservation public

record RoutedZelphObservationBatch : Set where
  constructor routed-zelph-observation-batch
  field
    subjectQidReference : String
    queryFamilyReference : String
    executionReceiptReference : String
    observations : List RoutedZelphRelationObservation
    diagnosticOnly : Bool
    diagnosticOnlyIsTrue : diagnosticOnly ≡ true
open RoutedZelphObservationBatch public

------------------------------------------------------------------------
-- The runtime's ordinary pruned type path requires soundness only.  Negative
-- completeness is intentionally not smuggled into this assembly.
------------------------------------------------------------------------

record NatZelphPeerPipelineInput : Set where
  constructor nat-zelph-peer-pipeline-input
  field
    routedObservations : RoutedZelphObservationBatch
    typePreservation : Preservation.QueryFamilySoundnessReceipt
    typeModule : TypeModule.TypeClosureSoundnessReceipt
    joinedItemSurface : Join.WikibaseZelphItemSurface
    peerAssessment : Peer.NatPeerCohortAssessment
    existingPressure : Weld.ExistingNatPressureAssessment
open NatZelphPeerPipelineInput public

record NatZelphPeerPipelineOutput : Set where
  constructor nat-zelph-peer-pipeline-output
  field
    typeModuleReference : String
    joinedSurfaceReference : String
    peerResidualReference : String
    weldedPressureReference : String
    routedObservationsRemainGraphEvidenceOnly : Bool
    routedObservationsRemainGraphEvidenceOnlyIsTrue :
      routedObservationsRemainGraphEvidenceOnly ≡ true
    positiveTypeSoundnessDoesNotCreateNegativeCompleteness : Bool
    positiveTypeSoundnessDoesNotCreateNegativeCompletenessIsTrue :
      positiveTypeSoundnessDoesNotCreateNegativeCompleteness ≡ true
    nativeAndGraphPlanesRemainDistinct : Bool
    nativeAndGraphPlanesRemainDistinctIsTrue : nativeAndGraphPlanesRemainDistinct ≡ true
    peerWeldChangesOnlyPeerCoordinate : Bool
    peerWeldChangesOnlyPeerCoordinateIsTrue : peerWeldChangesOnlyPeerCoordinate ≡ true
    authorityIsDiagnosticOnly : Bool
    authorityIsDiagnosticOnlyIsTrue : authorityIsDiagnosticOnly ≡ true
    promotionEvaluated : Bool
    promotionEvaluatedIsFalse : promotionEvaluated ≡ false
    editEffect : Bool
    editEffectIsFalse : editEffect ≡ false
open NatZelphPeerPipelineOutput public

------------------------------------------------------------------------
-- Firewalls for the exact runtime route.
------------------------------------------------------------------------

data RoutedRelationObservationIsNativeWikibaseStatement : Set where
data SoundPositiveTypeModuleImpliesNegativeTypeCompleteness : Set where
data TypeModuleImpliesEveryNativePropertyFamilyCovered : Set where
data JoinedItemSurfaceImpliesMigrationSafe : Set where
data ExactPeerResidualImpliesMigrationSafe : Set where
data PipelineCreatesPromotionAuthority : Set where
data PipelineCreatesEditAuthority : Set where

routedRelationDoesNotBecomeNativeStatement :
  RoutedRelationObservationIsNativeWikibaseStatement → ⊥
routedRelationDoesNotBecomeNativeStatement ()

positiveTypeSoundnessDoesNotGiveNegativeCompleteness :
  SoundPositiveTypeModuleImpliesNegativeTypeCompleteness → ⊥
positiveTypeSoundnessDoesNotGiveNegativeCompleteness ()

typeModuleDoesNotCoverEveryNativePropertyFamily :
  TypeModuleImpliesEveryNativePropertyFamilyCovered → ⊥
typeModuleDoesNotCoverEveryNativePropertyFamily ()

joinedSurfaceDoesNotProveMigrationSafety :
  JoinedItemSurfaceImpliesMigrationSafe → ⊥
joinedSurfaceDoesNotProveMigrationSafety ()

exactPeerDoesNotProveMigrationSafety :
  ExactPeerResidualImpliesMigrationSafe → ⊥
exactPeerDoesNotProveMigrationSafety ()

pipelineDoesNotCreatePromotionAuthority :
  PipelineCreatesPromotionAuthority → ⊥
pipelineDoesNotCreatePromotionAuthority ()

pipelineDoesNotCreateEditAuthority :
  PipelineCreatesEditAuthority → ⊥
pipelineDoesNotCreateEditAuthority ()

record NatZelphPeerPipelineBoundary : Set where
  constructor nat-zelph-peer-pipeline-boundary
  field
    transportPlanAndQueryResultAreDistinct : Bool
    routedResultRequiresExecutionReceipt : Bool
    routedP31P279CanFeedSoundTypeModule : Bool
    soundPositiveTypeResultCreatesNegativeCompleteness : Bool
    typeModuleReconstructsNativeStatements : Bool
    joinedSurfacePreservesTwoEvidencePlanes : Bool
    peerWeldRewritesOnlyPeerCoordinate : Bool
    pipelineCreatesMigrationSafety : Bool
    pipelineCreatesPromotion : Bool
    pipelineCreatesEdit : Bool

canonicalNatZelphPeerPipelineBoundary : NatZelphPeerPipelineBoundary
canonicalNatZelphPeerPipelineBoundary =
  nat-zelph-peer-pipeline-boundary
    true true true false false true true false false false

natZelphPeerPipelineStatement : String
natZelphPeerPipelineStatement =
  "The concrete Nat route begins after an actual routed Zelph execution produces receipt-bound normalized P31/P279 observations. Those graph observations may feed a query-family sound type module; positive soundness alone does not establish negative completeness. The graph module then joins a separate revision-pinned native Wikibase statement plane to form the item evidence surface, and the governed peer evaluator may replace only the peer_cohort residual of the existing Nat pressure assessment. Graph observations do not become native statements, and the pipeline creates no migration, promotion, or edit authority."
