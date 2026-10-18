module DASHI.Reasoning.TrialecticProductiveJoinDescentExact where

------------------------------------------------------------------------
-- THREE FIRST-ORDER DIALECTICAL GLUINGS + IRREDUCIBLE FACE
--
-- DASHI CONTRIBUTION
--
-- This file is the explicit A-B-C descent object requested by the relational
-- formalisation.  Each edge is an existing ProductiveDialecticalJoin; the face
-- is retained separately and is not reconstructed from the three edges.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.RelationalSelfStalkExact as Self
import DASHI.Governance.SexedHistoricalProductiveDialecticalFibreJoinExact as Join

data TriadicFaceKind : Set where
  reciprocalMediation : TriadicFaceKind
  unresolvedTriadicResidual : TriadicFaceKind
  coerciveTriadicConfiguration : TriadicFaceKind

record TrialecticDescentState (View : Set) : Set₁ where
  constructor trialectic-descent-state
  field
    vertexA vertexB vertexC : Self.SelfStalk View

    edgeAB : Join.ProductiveDialecticalJoin
    edgeBC : Join.ProductiveDialecticalJoin
    edgeCA : Join.ProductiveDialecticalJoin

    faceABC : TriadicFaceKind
    descentResidual : String
    orderHistoryReceipt : String

open TrialecticDescentState public

data DemoView : Set where
  demoView : DemoView

demoA : Self.SelfStalk DemoView
demoA =
  Self.self-stalk Self.contextAB demoView
    Self.highResolution Self.highAuthority
    "A relational self-stalk"

demoB : Self.SelfStalk DemoView
demoB =
  Self.self-stalk Self.contextBC demoView
    Self.highResolution Self.highAuthority
    "B relational self-stalk"

demoC : Self.SelfStalk DemoView
demoC =
  Self.self-stalk Self.contextABC demoView
    Self.highResolution Self.lowAuthority
    "C relational self-stalk"

sameEdgesDifferentFaceLeft : TrialecticDescentState DemoView
sameEdgesDifferentFaceLeft =
  trialectic-descent-state
    demoA demoB demoC
    Join.canonicalProductiveJoin
    Join.canonicalProductiveJoin
    Join.canonicalProductiveJoin
    reciprocalMediation
    "face residual A"
    "AB -> BC -> CA"

sameEdgesDifferentFaceRight : TrialecticDescentState DemoView
sameEdgesDifferentFaceRight =
  trialectic-descent-state
    demoA demoB demoC
    Join.canonicalProductiveJoin
    Join.canonicalProductiveJoin
    Join.canonicalProductiveJoin
    unresolvedTriadicResidual
    "face residual B"
    "AB -> BC -> CA"

data ThreeProductiveJoinsAreWholeTrialectic : Set where

threeProductiveJoinsDoNotBecomeWholeTrialectic :
  ThreeProductiveJoinsAreWholeTrialectic → ⊥
threeProductiveJoinsDoNotBecomeWholeTrialectic ()

record TrialecticProductiveJoinBoundary : Set where
  constructor trialectic-productive-join-boundary
  field
    threeEdgesUseExistingProductiveJoinOwner : Bool
    verticesRetainRelationshipIndexedSelf : Bool
    faceIsAdditionalCoordinate : Bool
    faceDefinedAsForcedSynthesis : Bool
    edgeAgreementErasesOrderHistory : Bool

canonicalTrialecticProductiveJoinBoundary :
  TrialecticProductiveJoinBoundary
canonicalTrialecticProductiveJoinBoundary =
  trialectic-productive-join-boundary true true true false false
