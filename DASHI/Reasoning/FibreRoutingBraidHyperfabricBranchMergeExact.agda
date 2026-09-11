module DASHI.Reasoning.FibreRoutingBraidHyperfabricBranchMergeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Reasoning.FibreRoutingGrokkingMoEBrainCrossPollinationExact as Routing
import DASHI.Core.BraidedEvidenceTraceBidiCrossPollination2026Exact as Braid
import DASHI.Combinatorics.ProofCarryingTextileHyperfabricExact as Textile
import DASHI.Reasoning.AristotleBranchMergeExact as Merge

------------------------------------------------------------------------
-- DYNAMIC FIBRE TOPOLOGY / BRAID / HYPERFABRIC CROSS-POLLINATION
--
-- The original Fly NDim family used eight declared structural coordinates:
-- direct forward/reverse, two-hop forward/reverse, common-input/common-output,
-- and signed forward/reverse.  Eight is therefore the cardinality of one
-- consumer-facing finite slice, not a theorem about the number of biological,
-- computational, or representational fibres.
--
-- This owner lifts the routing grammar from a flat family to an event-indexed
-- fibre hyperfabric in which strands may split directionally, cross while
-- retaining identity, and rejoin only through an explicit compatibility receipt.
------------------------------------------------------------------------

data FibreDirection : Set where
  forwardDirection : FibreDirection
  reverseDirection : FibreDirection
  lateralDirection : FibreDirection
  inheritedDirection : FibreDirection

data FibreEventKind : Set where
  continuationEvent : FibreEventKind
  splitEvent : FibreEventKind
  crossingEvent : FibreEventKind
  rejoinEvent : FibreEventKind
  terminationEvent : FibreEventKind

data FibreNode : Set where
  sourceFibre : FibreNode
  directForwardNode : FibreNode
  directReverseNode : FibreNode
  signedForwardNode : FibreNode
  signedReverseNode : FibreNode
  consumerJoinNode : FibreNode

record DirectedFibreEvent : Set where
  constructor directed-fibre-event
  field
    source : FibreNode
    target : FibreNode
    direction : FibreDirection
    kind : FibreEventKind
    provenance : String

open DirectedFibreEvent public

forwardSplit : DirectedFibreEvent
forwardSplit =
  directed-fibre-event
    sourceFibre directForwardNode forwardDirection splitEvent
    "directional branch from a retained source fibre"

reverseSplit : DirectedFibreEvent
reverseSplit =
  directed-fibre-event
    sourceFibre directReverseNode reverseDirection splitEvent
    "directional branch from the same retained source fibre"

record SplitReceipt
    (parent left right : FibreNode) : Set where
  constructor split-receipt
  field
    leftEvent : DirectedFibreEvent
    rightEvent : DirectedFibreEvent
    leftStartsAtParent : source leftEvent ≡ parent
    rightStartsAtParent : source rightEvent ≡ parent
    leftEndsAtChild : target leftEvent ≡ left
    rightEndsAtChild : target rightEvent ≡ right

open SplitReceipt public

canonicalDirectionalSplit :
  SplitReceipt sourceFibre directForwardNode directReverseNode
canonicalDirectionalSplit =
  split-receipt forwardSplit reverseSplit refl refl refl refl

------------------------------------------------------------------------
-- Crossing is braid-like coordination, not fusion.
------------------------------------------------------------------------

braidCoordinationWithoutFusion :
  Braid.coordinationWithoutFusion Braid.canonicalBraidedEvidenceBoundary ≡ true
braidCoordinationWithoutFusion = refl

data CrossingAutomaticallyFusesFibres : Set where

crossingDoesNotAutomaticallyFuseFibres : CrossingAutomaticallyFusesFibres → ⊥
crossingDoesNotAutomaticallyFuseFibres ()

------------------------------------------------------------------------
-- Rejoin is also not an identity collapse.  It requires an explicit receipt,
-- analogous to guarded branch reconciliation: compatible descendants may feed
-- one consumer while their branch histories remain distinguishable.
------------------------------------------------------------------------

record RejoinReceipt (left right targetNode : FibreNode) : Set where
  constructor rejoin-receipt
  field
    leftReference : String
    rightReference : String
    compatibilityReceipt : String
    leftIdentityRetained : Bool
    leftIdentityRetainedIsTrue : leftIdentityRetained ≡ true
    rightIdentityRetained : Bool
    rightIdentityRetainedIsTrue : rightIdentityRetained ≡ true

open RejoinReceipt public

canonicalConsumerRejoin :
  RejoinReceipt directForwardNode directReverseNode consumerJoinNode
canonicalConsumerRejoin =
  rejoin-receipt
    "direct-forward branch"
    "direct-reverse branch"
    "consumer-specific composition receipt; common target does not identify branch histories"
    true refl true refl

data RejoinImpliesBranchIdentity : Set where

rejoinDoesNotCollapseBranchIdentity : RejoinImpliesBranchIdentity → ⊥
rejoinDoesNotCollapseBranchIdentity ()

------------------------------------------------------------------------
-- The old eight-coordinate family is one flattened observation of a richer
-- branching fabric.  It remains a legitimate consumer basis, but its size is
-- not an invariant of the underlying fibre process.
------------------------------------------------------------------------

data OriginalNDimCoordinate : Set where
  directForward : OriginalNDimCoordinate
  directReverse : OriginalNDimCoordinate
  twoHopForward : OriginalNDimCoordinate
  twoHopReverse : OriginalNDimCoordinate
  commonInput : OriginalNDimCoordinate
  commonOutput : OriginalNDimCoordinate
  signedForward : OriginalNDimCoordinate
  signedReverse : OriginalNDimCoordinate

data EightIsUniversalFibreCardinality : Set where

eightIsNotUniversalFibreCardinality : EightIsUniversalFibreCardinality → ⊥
eightIsNotUniversalFibreCardinality ()

textileBranchMotifIsAvailable : Textile.ProofMotif
textileBranchMotifIsAvailable = Textile.branchMotif

record DynamicFibreBoundary : Set where
  constructor dynamic-fibre-boundary
  field
    originalEightIsDeclaredFiniteSlice : Bool
    originalEightIsDeclaredFiniteSliceIsTrue :
      originalEightIsDeclaredFiniteSlice ≡ true

    fibreCountMayDependOnContextTimeAndConsumer : Bool
    fibreCountMayDependOnContextTimeAndConsumerIsTrue :
      fibreCountMayDependOnContextTimeAndConsumer ≡ true

    directionalSplitIsRepresentable : Bool
    directionalSplitIsRepresentableIsTrue :
      directionalSplitIsRepresentable ≡ true

    crossingAutomaticallyFusesStrands : Bool
    crossingAutomaticallyFusesStrandsIsFalse :
      crossingAutomaticallyFusesStrands ≡ false

    compatibleBranchesMayRejoinForAConsumer : Bool
    compatibleBranchesMayRejoinForAConsumerIsTrue :
      compatibleBranchesMayRejoinForAConsumer ≡ true

    rejoinErasesBranchProvenance : Bool
    rejoinErasesBranchProvenanceIsFalse :
      rejoinErasesBranchProvenance ≡ false

    flatCompressionResultProvesUnderlyingTopologyIsOneStrand : Bool
    flatCompressionResultProvesUnderlyingTopologyIsOneStrandIsFalse :
      flatCompressionResultProvesUnderlyingTopologyIsOneStrand ≡ false

canonicalDynamicFibreBoundary : DynamicFibreBoundary
canonicalDynamicFibreBoundary =
  dynamic-fibre-boundary
    true refl
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- Donor alignment.
--
-- `FibreRoutingCarrier` remains the local routing/membership interface;
-- braided evidence contributes crossing-without-fusion; the textile owner
-- contributes an explicit branch motif; and Aristotle branch merge contributes
-- the guarded-reconciliation discipline.  None of those donors is identified
-- with biological axon branching or with the MaleCNS mechanism itself.
------------------------------------------------------------------------

routingMayRemainContextRelative :
  Routing.routingMayBeConsumerAndContextRelative
    Routing.canonicalFibreRoutingCrossPollinationBoundary ≡ true
routingMayRemainContextRelative = refl

aristotleMergeNeedsMoreThanVisibleEquality :
  Merge.sameObservedStateAutomaticallyMergeable
    Merge.canonicalAristotleBranchMergeBoundary ≡ false
aristotleMergeNeedsMoreThanVisibleEquality = refl
