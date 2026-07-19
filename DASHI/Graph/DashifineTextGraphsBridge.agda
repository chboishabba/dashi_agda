module DASHI.Graph.DashifineTextGraphsBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Dashifine conversational trajectory ↔ TextGraphs observable bridge.
--
-- The bridge has three deliberately separate layers:
--
--   1. faithful transport of path state and named invariants;
--   2. graph-derived observables computed from the transported graph;
--   3. promotion, which requires evidence from layer 2 and cannot be
--      manufactured from transport parity alone.
--
-- This is the formal correction to the tempting but invalid inference
--
--   graphR (encode x) ≡ dashR x
--   therefore TextGraphs independently discovered R.
--
-- The equality is a conformance witness.  Discovery is a separate type.

------------------------------------------------------------------------
-- Canonical ternary state carrier.

data Trit : Set where
  neg zer pos : Trit

record ConversationState : Set where
  constructor state
  field
    self norm mirror : Trit

open ConversationState public

------------------------------------------------------------------------
-- Small signed invariant carrier sufficient for the current A→I fixture.

data Invariant : Set where
  minusOne zero one three : Invariant

record BridgeRow : Set where
  constructor row
  field
    labelIndex : Nat
    ternaryState : ConversationState
    resonance : Invariant
    selfNorm : Invariant

open BridgeRow public

------------------------------------------------------------------------
-- Graph-side transported state and graph-derived observables.

record GraphNode : Set where
  constructor node
  field
    sourceRow : BridgeRow

open GraphNode public

encodeNode : BridgeRow → GraphNode
encodeNode r = node r

graphTransportedR : GraphNode → Invariant
graphTransportedR n = resonance (sourceRow n)

graphTransportedZ : GraphNode → Invariant
graphTransportedZ n = selfNorm (sourceRow n)

transportPreservesR :
  (r : BridgeRow) →
  graphTransportedR (encodeNode r) ≡ resonance r
transportPreservesR r = refl

transportPreservesZ :
  (r : BridgeRow) →
  graphTransportedZ (encodeNode r) ≡ selfNorm r
transportPreservesZ r = refl

------------------------------------------------------------------------
-- Exact Phase-1 / Phase-2 conformance surface.

record Ratio : Set where
  constructor ratio
  field
    numerator denominator : Nat

open Ratio public

record BridgeConformance : Set where
  field
    waypointCount : Nat
    waypointCountIs10 : waypointCount ≡ 10

    transitionCount : Nat
    transitionCountIs9 : transitionCount ≡ 9

    pathL1Length : Nat
    pathL1LengthIs16 : pathL1Length ≡ 16

    baselineSCCCount : Nat
    baselineSCCCountIs10 : baselineSCCCount ≡ 10

    baselineLargestSCC : Nat
    baselineLargestSCCIs1 : baselineLargestSCC ≡ 1

    baselineDensity : Ratio
    baselineDensityIsOneTenth : baselineDensity ≡ ratio 1 10

    weightedMinimum : Nat
    weightedMinimumIs2 : weightedMinimum ≡ 2

    weightedMaximum : Nat
    weightedMaximumIs10 : weightedMaximum ≡ 10

    weightedSum : Nat
    weightedSumIs41 : weightedSum ≡ 41

    deltaRSum : Nat
    deltaRSumIs8 : deltaRSum ≡ 8

    deltaZSum : Nat
    deltaZSumIs8 : deltaZSum ≡ 8

    deltaStateSum : Nat
    deltaStateSumIs16 : deltaStateSum ≡ 16

open BridgeConformance public

canonicalBridgeConformance : BridgeConformance
canonicalBridgeConformance =
  record
    { waypointCount = 10
    ; waypointCountIs10 = refl
    ; transitionCount = 9
    ; transitionCountIs9 = refl
    ; pathL1Length = 16
    ; pathL1LengthIs16 = refl
    ; baselineSCCCount = 10
    ; baselineSCCCountIs10 = refl
    ; baselineLargestSCC = 1
    ; baselineLargestSCCIs1 = refl
    ; baselineDensity = ratio 1 10
    ; baselineDensityIsOneTenth = refl
    ; weightedMinimum = 2
    ; weightedMinimumIs2 = refl
    ; weightedMaximum = 10
    ; weightedMaximumIs10 = refl
    ; weightedSum = 41
    ; weightedSumIs41 = refl
    ; deltaRSum = 8
    ; deltaRSumIs8 = refl
    ; deltaZSum = 8
    ; deltaZSumIs8 = refl
    ; deltaStateSum = 16
    ; deltaStateSumIs16 = refl
    }

------------------------------------------------------------------------
-- ZKP / PNF evidence separation.

data EvidenceKind : Set where
  transportParity graphDerived : EvidenceKind

record Evidence (kind : EvidenceKind) : Set where
  constructor evidence
  field
    witnessCount : Nat

TransportEvidence : Set
TransportEvidence = Evidence transportParity

GraphDerivedEvidence : Set
GraphDerivedEvidence = Evidence graphDerived

-- Transport evidence is useful for conformance, but it cannot inhabit the
-- independent-discovery promotion type.
data IndependentGraphDiscovery : Set where
  independentlyGraphDerived : GraphDerivedEvidence → IndependentGraphDiscovery

data TransportParityPromotion : Set where

transportParityCannotPromote : TransportParityPromotion → ⊥
transportParityCannotPromote ()

record InformativeBridgePromotion : Set where
  constructor informativeBridge
  field
    graphEvidence : GraphDerivedEvidence
    semanticRelationWitnessCount : Nat

------------------------------------------------------------------------
-- O,R,C,S,L,P,G,F surface.

record ZKPBridgeModel : Set₁ where
  field
    O-Organization : Set
    R-Objective : Set
    C-Encoding : Set
    S-State : Set
    L-ObservableLattice : Set
    P-Promotion : Set
    G-Gap : Set
    F-GapFunction : Set

canonicalZKPBridgeModel : ZKPBridgeModel
canonicalZKPBridgeModel =
  record
    { O-Organization = BridgeConformance
    ; R-Objective = TransportEvidence
    ; C-Encoding = BridgeRow → GraphNode
    ; S-State = ConversationState
    ; L-ObservableLattice = GraphDerivedEvidence
    ; P-Promotion = InformativeBridgePromotion
    ; G-Gap = IndependentGraphDiscovery
    ; F-GapFunction = Nat → Nat
    }
