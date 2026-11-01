module DASHI.Biology.AnimalCommunicationSharedWorldAVAssociationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Biology.AnimalCommunicationMultiObserverVisualBridgeExact as Visual
import DASHI.Biology.AnimalCommunicationPassiveAcousticLocalizationExact as Acoustic
import DASHI.Biology.AnimalCommunicationSceneObservationExact as Scene

------------------------------------------------------------------------
-- SHARED-WORLD AUDIOVISUAL ASSOCIATION
--
-- Visual world tracks and passive acoustic localization hypotheses may be
-- compared inside one candidate world coordinate fibre.  The result remains
-- a many-to-many association surface until same-object evidence pays a
-- stronger claim.
------------------------------------------------------------------------

record SharedWorldAVAssociationReceipt : Set where
  constructor shared-world-av-association-receipt
  field
    sceneReference : String
    visualTrackReference : String
    visualWorldRegionReference : String
    acousticEventReference : String
    acousticWorldRegionReference : String
    spatialOverlapReference : String
    temporalAlignmentReference : String
    beakBodySynchronyReference : String
    trackContinuityReference : String
    callFamilyCompatibilityReference : String
    propagationConsistencyReference : String
    worldWeldResidualReference : String
    associationResidualReference : String
    provenanceReference : String
    sameWorldCoordinateFibrePaid : Bool
    sameObjectIdentityPaid : Bool
    vocalEmitterIdentityPaid : Bool
    semanticMeaningPaid : Bool
    manyToManyAssociationRetained : Bool

open SharedWorldAVAssociationReceipt public

record SharedWorldAssociationGraph : Set where
  constructor shared-world-association-graph
  field
    sceneReference : String
    visualTrackReferences : List String
    acousticEventReferences : List String
    candidateAssociationReceipts : List SharedWorldAVAssociationReceipt
    unresolvedVisualReferences : List String
    unresolvedAcousticReferences : List String
    graphProvenanceReference : String

open SharedWorldAssociationGraph public

------------------------------------------------------------------------
-- Finite obstruction: equal spatial overlap does not determine same-emitter
-- identity.  Two worlds can expose the same visual/acoustic overlap surface
-- while differing on whether the visible animal produced the call.
------------------------------------------------------------------------

data AVWorld : Set where
  visibleBirdProducedCall : AVWorld
  hiddenBirdProducedCall : AVWorld

data AVOverlapSurface : Set where
  sameWorldRegionsOverlap : AVOverlapSurface

data AVQuery : Set where
  sameEmitterQuery : AVQuery

data AVAnswer : Set where
  sameEmitter : AVAnswer
  differentEmitter : AVAnswer

avOverlapProjection : AVWorld → AVOverlapSurface
avOverlapProjection world = sameWorldRegionsOverlap

avAnswer : AVQuery → AVWorld → AVAnswer
avAnswer sameEmitterQuery visibleBirdProducedCall = sameEmitter
avAnswer sameEmitterQuery hiddenBirdProducedCall = differentEmitter

avSemantics : Query.QuerySemantics AVWorld AVQuery AVAnswer
avSemantics = Query.querySemantics avAnswer

spatialOverlapSameEmitterDefect :
  Query.QueryAdequacyDefect avOverlapProjection avSemantics sameEmitterQuery
spatialOverlapSameEmitterDefect =
  Query.queryAdequacyDefect
    visibleBirdProducedCall
    hiddenBirdProducedCall
    refl
    (λ ())

spatialOverlapDoesNotCreateSameEmitter :
  Query.AdequateFor avOverlapProjection avSemantics sameEmitterQuery → ⊥
spatialOverlapDoesNotCreateSameEmitter =
  Query.queryAdequacyDefectBlocksFactorisation spatialOverlapSameEmitterDefect

------------------------------------------------------------------------
-- Additional fail-closed boundaries.
------------------------------------------------------------------------

data LowWorldWeldResidualCreatesSameAnimalPermission : Set where

data AVAssociationCreatesSemanticMeaningPermission : Set where

data SameWorldTrackCreatesIndividualIdentityPermission : Set where

lowWorldWeldResidualDoesNotCreateSameAnimal :
  LowWorldWeldResidualCreatesSameAnimalPermission → ⊥
lowWorldWeldResidualDoesNotCreateSameAnimal ()

avAssociationDoesNotCreateSemanticMeaning :
  AVAssociationCreatesSemanticMeaningPermission → ⊥
avAssociationDoesNotCreateSemanticMeaning ()

sameWorldTrackDoesNotCreateIndividualIdentity :
  SameWorldTrackCreatesIndividualIdentityPermission → ⊥
sameWorldTrackDoesNotCreateIndividualIdentity ()

record SharedWorldAVAssociationBoundary : Set where
  constructor shared-world-av-association-boundary
  field
    visualAndAcousticUseSharedCandidateWorld : Bool
    spatialOverlapIsAssociationEvidence : Bool
    spatialOverlapIsSameObjectProof : Bool
    beakBodySynchronyMayRefineAssociation : Bool
    propagationConsistencyMayRefineAssociation : Bool
    trackContinuityMayRefineAssociation : Bool
    unresolvedAssociationsRemainFirstClass : Bool
    manyToManyAssociationRetained : Bool
    associationDoesNotCreateMeaning : Bool

open SharedWorldAVAssociationBoundary public

canonicalSharedWorldAVAssociationBoundary : SharedWorldAVAssociationBoundary
canonicalSharedWorldAVAssociationBoundary =
  shared-world-av-association-boundary
    true true false true true true true true true

visualBridgeOwnerReused : String
visualBridgeOwnerReused =
  "DASHI.Biology.AnimalCommunicationMultiObserverVisualBridgeExact"

passiveLocalizationOwnerReused : String
passiveLocalizationOwnerReused =
  "DASHI.Biology.AnimalCommunicationPassiveAcousticLocalizationExact"

associationReading : String
associationReading =
  "Trail-camera/shared-world visual tracks and passive acoustic localization hypotheses meet in one candidate world coordinate fibre. Spatial overlap, temporal alignment, beak/body synchrony, propagation consistency and track continuity may shrink a many-to-many AV relation; none of them alone creates same-object identity, unique vocal-emitter identity, individual identity or semantic meaning."
