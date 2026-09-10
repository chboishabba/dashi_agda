module DASHI.Cognition.PNF.SensibLawBroadcastDiscourseGraphCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Cognition.PNF.SensibLawTranscriptBoundaryFibreClassifierExact as Fibre
import DASHI.Cognition.PNF.SensibLawTranscriptBoundaryPNFWorldManifoldExact as Manifold

------------------------------------------------------------------------
-- Provenance-bearing graph compilation from boundary manifolds.
------------------------------------------------------------------------

data SpeakerCertainty : Set where
  unresolvedSpeaker : SpeakerCertainty
  candidateSpeaker : SpeakerCertainty
  likelySpeaker : SpeakerCertainty
  verifiedSpeaker : SpeakerCertainty

record DiscourseSpanNode : Set where
  constructor discourseSpanNode
  field
    spanId : String
    sourceStartReference : String
    sourceEndReference : String
    sentenceReference : String
    speakerReference : String
    speakerCertainty : SpeakerCertainty
    claimReference : String
    provenanceReference : String

open DiscourseSpanNode public

record BoundaryNode : Set where
  constructor boundaryNode
  field
    boundaryId : String
    sentenceReference : String
    splitReference : String
    manifoldReference : String
    paretoFibreReference : String
    selectedProjectionReference : String
    residualFibreReference : String
    pnfResidualReference : String
    candidateOnly : Bool

open BoundaryNode public

data DiscourseEdgeKind : Set where
  speakerTransition : DiscourseEdgeKind
  reporterQuoteEdge : DiscourseEdgeKind
  attributionNestingEdge : DiscourseEdgeKind
  asrRepairEdge : DiscourseEdgeKind
  rhetoricalContrastEdge : DiscourseEdgeKind
  unresolvedBoundaryEdge : DiscourseEdgeKind

record DiscourseEdge : Set where
  constructor discourseEdge
  field
    edgeId : String
    fromReference : String
    toReference : String
    kind : DiscourseEdgeKind
    boundaryReference : String
    evidenceReference : String

open DiscourseEdge public

record BroadcastDiscourseGraph : Set where
  constructor broadcastDiscourseGraph
  field
    sourceSha256 : String
    spans : List DiscourseSpanNode
    boundaries : List BoundaryNode
    edges : List DiscourseEdge
    unresolvedResidualReference : String
    compilerSchema : String

open BroadcastDiscourseGraph public

------------------------------------------------------------------------
-- Projection is allowed only after the manifold layer.  A singleton Pareto
-- front may propose one edge kind, but it still cannot verify speaker identity.
------------------------------------------------------------------------

data SingletonParetoFront : Set where
  singletonParetoFront : Fibre.BoundaryFibreKind → SingletonParetoFront

projectEdgeKind : SingletonParetoFront → DiscourseEdgeKind
projectEdgeKind (singletonParetoFront Fibre.speakerCut) = speakerTransition
projectEdgeKind (singletonParetoFront Fibre.reporterQuoteHandoff) = reporterQuoteEdge
projectEdgeKind (singletonParetoFront Fibre.attributionNesting) = attributionNestingEdge
projectEdgeKind (singletonParetoFront Fibre.asrDamage) = asrRepairEdge
projectEdgeKind (singletonParetoFront Fibre.rhetoricalPivot) = rhetoricalContrastEdge

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data MultiPointFrontMustChooseWinner : Set where
multiPointFrontDoesNotRequireWinner : MultiPointFrontMustChooseWinner → ⊥
multiPointFrontDoesNotRequireWinner ()

data SpeakerTransitionVerifiesIdentity : Set where
speakerTransitionDoesNotVerifyIdentity : SpeakerTransitionVerifiesIdentity → ⊥
speakerTransitionDoesNotVerifyIdentity ()

data GraphCompilerErasesResidual : Set where
graphCompilerDoesNotEraseResidual : GraphCompilerErasesResidual → ⊥
graphCompilerDoesNotEraseResidual ()

data ReconstructedSpanCreatesClaimTruth : Set where
reconstructedSpanDoesNotCreateClaimTruth : ReconstructedSpanCreatesClaimTruth → ⊥
reconstructedSpanDoesNotCreateClaimTruth ()

record BroadcastGraphCompilerBoundary : Set where
  constructor broadcastGraphCompilerBoundary
  field
    consumesManifoldNotScalarWinner : Bool
    singletonFrontMayProposeEdge : Bool
    multiPointFrontRemainsUnresolved : Bool
    residualFibresRetained : Bool
    speakerCertaintyIndependent : Bool
    graphMayFeedReconstructedPNF : Bool
    graphCreatesWorldTruth : Bool

canonicalBroadcastGraphCompilerBoundary : BroadcastGraphCompilerBoundary
canonicalBroadcastGraphCompilerBoundary =
  broadcastGraphCompilerBoundary true true true true true true false

manifoldBoundaryAnchor : Manifold.PNFWorldManifoldBoundary
manifoldBoundaryAnchor = Manifold.canonicalPNFWorldManifoldBoundary
