module DASHI.Physics.Moonshine.SSPMoonshineTraceFibreIntegrationExact where

open import DASHI.Core.Prelude

import DASHI.Core.IndexedWeaveHyperfabricExact as Indexed
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as SSP
import DASHI.Biology.SSPIndexedWeaveHyperfabricExact as SSPWeave
import DASHI.Physics.Moonshine.MoonshineTraceIndexedWeaveExact as Trace

------------------------------------------------------------------------
-- Exact bounded cross-pollination of SSP lane fibres with trace fibres.
--
-- The index records both an SSP lane and an observed trace profile.  The state
-- retains the lane carrier together with one hidden state in that trace fibre.
-- Paths transport the SSP component while preserving the trace profile by an
-- equality witness.  Residuals retain both the SSP orientation and the hidden
-- trace tag.
--
-- This is a finite product theorem.  It does not prove that Monster
-- representations canonically identify or couple the fifteen Ogg-prime lanes.
------------------------------------------------------------------------

SSPTraceIndex : Set
SSPTraceIndex = SSP.SSPPrime × Trace.TraceProfile

SSPTraceState : SSPTraceIndex → Set
SSPTraceState index =
  SSPWeave.SSPWeaveState (fst index)
  × Trace.TraceFibre (snd index)

SSPTracePath : SSPTraceIndex → SSPTraceIndex → Set
SSPTracePath source target =
  SSPWeave.SSPWeavePath (fst source) (fst target)
  × Trace.TracePath (snd source) (snd target)

identitySSPTracePath :
  (index : SSPTraceIndex) →
  SSPTracePath index index
identitySSPTracePath index =
  SSPWeave.identitySSPPath (fst index) ,
  Trace.identityTracePath (snd index)

infixr 40 _thenSSPTrace_

_thenSSPTrace_ :
  {source middle target : SSPTraceIndex} →
  SSPTracePath middle target →
  SSPTracePath source middle →
  SSPTracePath source target
_thenSSPTrace_ (qLane , qTrace) (pLane , pTrace) =
  SSPWeave._thenSSP_ qLane pLane ,
  Trace._thenTrace_ qTrace pTrace

sspTracePathIdLeft :
  {source target : SSPTraceIndex} →
  (path : SSPTracePath source target) →
  identitySSPTracePath target thenSSPTrace path ≡ path
sspTracePathIdLeft (lanePath , refl)
  rewrite SSPWeave.sspPathIdLeft lanePath = refl

sspTracePathIdRight :
  {source target : SSPTraceIndex} →
  (path : SSPTracePath source target) →
  path thenSSPTrace identitySSPTracePath source ≡ path
sspTracePathIdRight (lanePath , refl)
  rewrite SSPWeave.sspPathIdRight lanePath = refl

sspTracePathAssoc :
  {i j k l : SSPTraceIndex} →
  (r : SSPTracePath k l) →
  (q : SSPTracePath j k) →
  (p : SSPTracePath i j) →
  (r thenSSPTrace q) thenSSPTrace p
  ≡ r thenSSPTrace (q thenSSPTrace p)
sspTracePathAssoc (rLane , refl) (qLane , refl) (pLane , refl)
  rewrite SSPWeave.sspPathAssoc rLane qLane pLane = refl

transportSSPTrace :
  {source target : SSPTraceIndex} →
  SSPTracePath source target →
  SSPTraceState source →
  SSPTraceState target
transportSSPTrace (lanePath , refl) (laneState , traceState) =
  SSPWeave.transportSSP lanePath laneState , traceState

transportSSPTraceIdentity :
  (index : SSPTraceIndex) →
  (state : SSPTraceState index) →
  transportSSPTrace (identitySSPTracePath index) state ≡ state
transportSSPTraceIdentity index (laneState , traceState)
  rewrite SSPWeave.transportSSPIdentity (fst index) laneState = refl

transportSSPTraceComposition :
  {source middle target : SSPTraceIndex} →
  (q : SSPTracePath middle target) →
  (p : SSPTracePath source middle) →
  (state : SSPTraceState source) →
  transportSSPTrace (q thenSSPTrace p) state
  ≡ transportSSPTrace q (transportSSPTrace p state)
transportSSPTraceComposition
  (qLane , refl) (pLane , refl) (laneState , traceState)
  rewrite SSPWeave.transportSSPComposition qLane pLane laneState = refl

SSPTraceResidual : SSPTraceIndex → Set
SSPTraceResidual index =
  SSP.FibreOrientation × Trace.HiddenTraceTag

sspTraceStateResidual :
  (index : SSPTraceIndex) →
  SSPTraceState index →
  SSPTraceResidual index
sspTraceStateResidual index (laneState , traceState) =
  SSP.mediatedOrientation , Trace.hiddenTagOfFibre traceState

sspTraceResidualAfter :
  {source target : SSPTraceIndex} →
  SSPTracePath source target →
  SSPTraceState source →
  SSPTraceResidual target
sspTraceResidualAfter (lanePath , refl) (laneState , traceState) =
  SSPWeave.pathOrientation lanePath , Trace.hiddenTagOfFibre traceState

sspTraceResidualIdentity :
  (index : SSPTraceIndex) →
  (state : SSPTraceState index) →
  sspTraceResidualAfter (identitySSPTracePath index) state
  ≡ sspTraceStateResidual index state
sspTraceResidualIdentity index state = refl

canonicalSSPMoonshineTraceIndexedWeave :
  Indexed.IndexedWeave SSPTraceIndex SSPTraceState
canonicalSSPMoonshineTraceIndexedWeave =
  record
    { Path = SSPTracePath
    ; idPath = identitySSPTracePath
    ; _∙_ = _thenSSPTrace_
    ; pathIdLeft = sspTracePathIdLeft
    ; pathIdRight = sspTracePathIdRight
    ; pathAssoc = sspTracePathAssoc
    ; transport = transportSSPTrace
    ; transportId = transportSSPTraceIdentity
    ; transportComp = transportSSPTraceComposition
    ; Residual = SSPTraceResidual
    ; stateResidual = sspTraceStateResidual
    ; residualAfter = sspTraceResidualAfter
    ; residualId = sspTraceResidualIdentity
    }

traceAStateInLane :
  (lane : SSP.SSPPrime) →
  SSPWeave.SSPWeaveState lane →
  Trace.TraceFibre Trace.tracePrefixA →
  SSPTraceState (lane , Trace.tracePrefixA)
traceAStateInLane lane laneState traceState = laneState , traceState

sameObservedTraceRemainsHiddenDistinctInEveryLane :
  (lane : SSP.SSPPrime) →
  (laneState : SSPWeave.SSPWeaveState lane) →
  traceAStateInLane lane laneState Trace.hiddenStateAInTraceA
  ≡ traceAStateInLane lane laneState Trace.hiddenStateBInTraceA
  → ⊥
sameObservedTraceRemainsHiddenDistinctInEveryLane lane laneState ()

inverseLaneTransportRetainsHiddenTraceTag :
  {sourceLane targetLane : SSP.SSPPrime} →
  (laneState : SSPWeave.SSPWeaveState sourceLane) →
  sspTraceResidualAfter
    ( SSPWeave.lanePath
        {source = sourceLane}
        {target = targetLane}
        SSP.inverseOrientation
    , refl
    )
    (laneState , Trace.hiddenStateAInTraceA)
  ≡ SSP.inverseOrientation , Trace.tagA
inverseLaneTransportRetainsHiddenTraceTag laneState = refl

record SSPMoonshineCompatibilityBoundary : Set where
  constructor sspMoonshineCompatibilityBoundary
  field
    boundedIndexedProductConstructed : Bool
    boundedIndexedProductConstructedIsTrue :
      boundedIndexedProductConstructed ≡ true
    hiddenTraceMultiplicitySurvivesEveryLane :
      (lane : SSP.SSPPrime) →
      (laneState : SSPWeave.SSPWeaveState lane) →
      traceAStateInLane lane laneState Trace.hiddenStateAInTraceA
      ≡ traceAStateInLane lane laneState Trace.hiddenStateBInTraceA
      → ⊥
    MonsterSuppliesCanonicalCrossLaneCompatibility : Bool
    MonsterSuppliesCanonicalCrossLaneCompatibilityIsFalse :
      MonsterSuppliesCanonicalCrossLaneCompatibility ≡ false

canonicalSSPMoonshineCompatibilityBoundary :
  SSPMoonshineCompatibilityBoundary
canonicalSSPMoonshineCompatibilityBoundary =
  sspMoonshineCompatibilityBoundary
    true refl
    sameObservedTraceRemainsHiddenDistinctInEveryLane
    false refl
