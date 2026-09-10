module DASHI.Cognition.PNF.SensibLawBroadcastDiscourseGraphCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Cognition.PNF.SensibLawTranscriptBoundaryFibreClassifierExact as Fibre
import DASHI.Cognition.PNF.SensibLawTranscriptBoundaryPNFWorldManifoldExact as Manifold

------------------------------------------------------------------------
-- Provenance-bearing graph compilation from boundary manifolds.
-- Runtime v2 keeps PNF structural topology on each boundary node so downstream
-- consumers can veto a projection without recomputing or scalarising it.
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

record BoundaryPNFTopology : Set where
  constructor boundaryPNFTopology
  field
    subjectCrossings : Nat
    objectCrossings : Nat
    clauseCrossings : Nat
    coordinationCrossings : Nat
    negationSideShiftReference : String
    modalitySideShiftReference : String

open BoundaryPNFTopology public

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
    pnfTopology : BoundaryPNFTopology
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
-- Projection is allowed only after the manifold layer. A singleton Pareto
-- front may propose one edge kind, but later consumers retain the independent
-- PNF topology and may reject that proposal for their own obligation.
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

data GraphProjectionOverridesPNFTopology : Set where
graphProjectionDoesNotOverridePNFTopology : GraphProjectionOverridesPNFTopology → ⊥
graphProjectionDoesNotOverridePNFTopology ()

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
    pnfTopologyRetainedOnBoundary : Bool
    downstreamConsumerMayVetoProjection : Bool
    speakerCertaintyIndependent : Bool
    graphMayFeedReconstructedPNF : Bool
    graphCreatesWorldTruth : Bool

canonicalBroadcastGraphCompilerBoundary : BroadcastGraphCompilerBoundary
canonicalBroadcastGraphCompilerBoundary =
  broadcastGraphCompilerBoundary true true true true true true true true false

manifoldBoundaryAnchor : Manifold.PNFWorldManifoldBoundary
manifoldBoundaryAnchor = Manifold.canonicalPNFWorldManifoldBoundary
