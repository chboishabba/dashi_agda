module DASHI.Reasoning.Trialectic369RubikRefinementExact where

------------------------------------------------------------------------
-- TRIALECTIC OBSERVER MATRIX <-> RANK-3 RECURSIVE HYPERVOXEL ADDRESS
--
-- DASHI CONTRIBUTION
--
-- One observer row is three SSP trits, hence exactly one rank-3 AxisBlock.
-- The three rows A/B/C can therefore be used as three successive refinement
-- blocks:
--
--   root --A--> depth1 --B--> depth2 --C--> depth3.
--
-- This gives an exact carrier bijection
--
--   ObserverMatrix3 SSPTrit  <->  TernaryAddress 3 3
--
-- with 27 choices at each refinement step and 27^3 = 19683 total addresses.
-- The ordering A then B then C is a declared DASHI chart; it does not claim
-- that participant order is intrinsic geometry.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Reasoning.TrialecticObserverMatrix369Exact as Observer
import DASHI.Reasoning.Trialectic369HypervoxelUltrametricExact as Bridge
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric
import DASHI.Foundations.RecursiveRadixHypervoxel as Hyper

tritToAxis3 : SSP.SSPTrit -> Hyper.Axis3
tritToAxis3 SSP.sspNegOne = Hyper.axis-low
tritToAxis3 SSP.sspZero = Hyper.axis-mid
tritToAxis3 SSP.sspPosOne = Hyper.axis-high

axis3ToTrit : Hyper.Axis3 -> SSP.SSPTrit
axis3ToTrit Hyper.axis-low = SSP.sspNegOne
axis3ToTrit Hyper.axis-mid = SSP.sspZero
axis3ToTrit Hyper.axis-high = SSP.sspPosOne

tritAxisRoundTrip :
  (trit : SSP.SSPTrit) ->
  axis3ToTrit (tritToAxis3 trit) ≡ trit
tritAxisRoundTrip SSP.sspNegOne = refl
tritAxisRoundTrip SSP.sspZero = refl
tritAxisRoundTrip SSP.sspPosOne = refl

axisTritRoundTrip :
  (axis : Hyper.Axis3) ->
  tritToAxis3 (axis3ToTrit axis) ≡ axis
axisTritRoundTrip Hyper.axis-low = refl
axisTritRoundTrip Hyper.axis-mid = refl
axisTritRoundTrip Hyper.axis-high = refl

rowToRank3Block :
  Fabric.Ternary27Point ->
  Hyper.AxisBlock 3
rowToRank3Block (Fabric.ternary27Point x y z) =
  Hyper.block-cons
    (tritToAxis3 x)
    (Hyper.block-cons
      (tritToAxis3 y)
      (Hyper.block-cons
        (tritToAxis3 z)
        Hyper.block-root))

rank3BlockToRow :
  Hyper.AxisBlock 3 ->
  Fabric.Ternary27Point
rank3BlockToRow
  (Hyper.block-cons x
    (Hyper.block-cons y
      (Hyper.block-cons z Hyper.block-root))) =
  Fabric.ternary27Point
    (axis3ToTrit x)
    (axis3ToTrit y)
    (axis3ToTrit z)

rowBlockRoundTrip :
  (row : Fabric.Ternary27Point) ->
  rank3BlockToRow (rowToRank3Block row) ≡ row
rowBlockRoundTrip
  (Fabric.ternary27Point SSP.sspNegOne y z)
  rewrite tritAxisRoundTrip y | tritAxisRoundTrip z = refl
rowBlockRoundTrip
  (Fabric.ternary27Point SSP.sspZero y z)
  rewrite tritAxisRoundTrip y | tritAxisRoundTrip z = refl
rowBlockRoundTrip
  (Fabric.ternary27Point SSP.sspPosOne y z)
  rewrite tritAxisRoundTrip y | tritAxisRoundTrip z = refl

blockRowRoundTrip :
  (block : Hyper.AxisBlock 3) ->
  rowToRank3Block (rank3BlockToRow block) ≡ block
blockRowRoundTrip
  (Hyper.block-cons Hyper.axis-low
    (Hyper.block-cons y
      (Hyper.block-cons z Hyper.block-root)))
  rewrite axisTritRoundTrip y | axisTritRoundTrip z = refl
blockRowRoundTrip
  (Hyper.block-cons Hyper.axis-mid
    (Hyper.block-cons y
      (Hyper.block-cons z Hyper.block-root)))
  rewrite axisTritRoundTrip y | axisTritRoundTrip z = refl
blockRowRoundTrip
  (Hyper.block-cons Hyper.axis-high
    (Hyper.block-cons y
      (Hyper.block-cons z Hyper.block-root)))
  rewrite axisTritRoundTrip y | axisTritRoundTrip z = refl

observerToDepth3Address :
  Observer.ObserverMatrix3 SSP.SSPTrit ->
  Hyper.TernaryAddress 3 3
observerToDepth3Address matrix =
  Hyper.address-refine
    (Hyper.address-refine
      (Hyper.address-refine
        Hyper.address-root
        (rowToRank3Block (Bridge.observerRowA matrix)))
      (rowToRank3Block (Bridge.observerRowB matrix)))
    (rowToRank3Block (Bridge.observerRowC matrix))

depth3AddressToObserver :
  Hyper.TernaryAddress 3 3 ->
  Observer.ObserverMatrix3 SSP.SSPTrit
depth3AddressToObserver
  (Hyper.address-refine
    (Hyper.address-refine
      (Hyper.address-refine Hyper.address-root rowA)
      rowB)
    rowC) =
  Observer.observerMatrix3
    (Fabric.x (rank3BlockToRow rowA))
    (Fabric.y (rank3BlockToRow rowA))
    (Fabric.z (rank3BlockToRow rowA))
    (Fabric.x (rank3BlockToRow rowB))
    (Fabric.y (rank3BlockToRow rowB))
    (Fabric.z (rank3BlockToRow rowB))
    (Fabric.x (rank3BlockToRow rowC))
    (Fabric.y (rank3BlockToRow rowC))
    (Fabric.z (rank3BlockToRow rowC))

observerAddressRoundTrip :
  (matrix : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  depth3AddressToObserver (observerToDepth3Address matrix) ≡ matrix
observerAddressRoundTrip
  (Observer.observerMatrix3
    aa ab ac ba bb bc ca cb cc)
  rewrite rowBlockRoundTrip (Fabric.ternary27Point aa ab ac)
        | rowBlockRoundTrip (Fabric.ternary27Point ba bb bc)
        | rowBlockRoundTrip (Fabric.ternary27Point ca cb cc) = refl

addressObserverRoundTrip :
  (address : Hyper.TernaryAddress 3 3) ->
  observerToDepth3Address (depth3AddressToObserver address) ≡ address
addressObserverRoundTrip
  (Hyper.address-refine
    (Hyper.address-refine
      (Hyper.address-refine Hyper.address-root rowA)
      rowB)
    rowC)
  rewrite blockRowRoundTrip rowA
        | blockRowRoundTrip rowB
        | blockRowRoundTrip rowC = refl

------------------------------------------------------------------------
-- Prefix/coarsening views: remove C, then B, then A.
------------------------------------------------------------------------

observerABPrefix :
  Observer.ObserverMatrix3 SSP.SSPTrit ->
  Hyper.TernaryAddress 3 2
observerABPrefix matrix =
  Hyper.coarsen (observerToDepth3Address matrix)

observerAPrefix :
  Observer.ObserverMatrix3 SSP.SSPTrit ->
  Hyper.TernaryAddress 3 1
observerAPrefix matrix =
  Hyper.coarsen (observerABPrefix matrix)

observerRoot :
  Observer.ObserverMatrix3 SSP.SSPTrit ->
  Hyper.TernaryAddress 3 0
observerRoot matrix =
  Hyper.coarsen (observerAPrefix matrix)

observerABPrefixExact :
  (matrix : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  observerABPrefix matrix
  ≡
  Hyper.address-refine
    (Hyper.address-refine
      Hyper.address-root
      (rowToRank3Block (Bridge.observerRowA matrix)))
    (rowToRank3Block (Bridge.observerRowB matrix))
observerABPrefixExact matrix = refl

observerAPrefixExact :
  (matrix : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  observerAPrefix matrix
  ≡
  Hyper.address-refine
    Hyper.address-root
    (rowToRank3Block (Bridge.observerRowA matrix))
observerAPrefixExact matrix = refl

observerRootExact :
  (matrix : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  observerRoot matrix ≡ Hyper.address-root
observerRootExact matrix = refl

------------------------------------------------------------------------
-- Exact cardinality receipts inherited from the existing hierarchy.
------------------------------------------------------------------------

oneRowDepthOneHas27Addresses :
  Hyper.siteCount 3 1 ≡ 27
oneRowDepthOneHas27Addresses =
  Hyper.rank3Depth1Sites

twoRowDepthTwoHas729Addresses :
  Hyper.siteCount 3 2 ≡ 729
twoRowDepthTwoHas729Addresses =
  Hyper.rank3Depth2Sites

threeRowObserverFabricHas19683States :
  Bridge.trialecticFabricStateCount ≡ 19683
threeRowObserverFabricHas19683States =
  Bridge.trialecticFabricStateCountIs19683

data ParticipantOrderIsIntrinsicRubikGeometry : Set where
data AddressDepthIsPsychologicalDevelopmentStage : Set where
data CoarseningMeansErasingParticipant : Set where

participantOrderIsNotPromotedToIntrinsicRubikGeometry :
  ParticipantOrderIsIntrinsicRubikGeometry -> ⊥
participantOrderIsNotPromotedToIntrinsicRubikGeometry ()

addressDepthIsNotPromotedToPsychologicalDevelopmentStage :
  AddressDepthIsPsychologicalDevelopmentStage -> ⊥
addressDepthIsNotPromotedToPsychologicalDevelopmentStage ()

coarseningIsChartForgetfulnessNotParticipantErasure :
  CoarseningMeansErasingParticipant -> ⊥
coarseningIsChartForgetfulnessNotParticipantErasure ()

record Trialectic369RubikRefinementBoundary : Set where
  constructor trialectic-369-rubik-refinement-boundary
  field
    observerRowEqualsRank3ChildBlockAsCarrier : Bool
    threeRowsGiveDepth3AddressBijection : Bool
    coarseningDropsSuccessiveRowBlocks : Bool
    depthOneCount27 : Bool
    depthTwoCount729 : Bool
    wholeFabricCount19683 : Bool
    participantOrderClaimedIntrinsic : Bool
    addressDepthClaimedPsychologicalStage : Bool

canonicalTrialectic369RubikRefinementBoundary :
  Trialectic369RubikRefinementBoundary
canonicalTrialectic369RubikRefinementBoundary =
  trialectic-369-rubik-refinement-boundary
    true true true true true true false false
