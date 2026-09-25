module DASHI.Reasoning.Trialectic369HypervoxelUltrametricExact where

------------------------------------------------------------------------
-- TRIALECTIC OBSERVER MATRIX <-> BASE369 T^9 HYPERFABRIC
--
-- DASHI CONTRIBUTION
--
-- This module closes the carrier theorem that was previously only recorded as
-- a shape fit:
--
--   ObserverMatrix3 SSPTrit
--       <-> NineTrits
--       <-> TernaryHyperformalPoint
--       =   (T^3)^3.
--
-- The rechart is exact and two-sided.  Semantic roles are NOT thereby
-- identified: the existing Base369 blocks are interaction/appraisal blocks,
-- whereas this chart uses the three observer rows A/B/C.
--
-- The exact rechart allows the canonical finite prefix ultrametric on
-- Vec Trit 9 to be transported onto the observer matrix.  Hence the trialectic
-- carrier inherits both:
--
--   d(X,Z) <= max(d(X,Y), d(Y,Z))
--
-- and the strict-leg ultrametric isosceles consequence:
--
--   d(X,Y) < d(Y,Z)  ->  d(X,Z) = d(Y,Z).
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_; _<_; _⊔_)
open import Data.Vec using (Vec; []; _∷_)

import DASHI.Algebra.Trit as Trit
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Reasoning.TrialecticObserverMatrix369Exact as Observer
import DASHI.Foundations.Base369NineCoordinateAggregateBridgeExact as Nine
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric
import DASHI.Metric.AgreementUltrametric as Metric

------------------------------------------------------------------------
-- 1. Literal row hypervoxels.
------------------------------------------------------------------------

observerRowA :
  Observer.ObserverMatrix3 SSP.SSPTrit ->
  Fabric.Ternary27Point
observerRowA matrix =
  Fabric.ternary27Point
    (Observer.aA matrix)
    (Observer.aB matrix)
    (Observer.aC matrix)

observerRowB :
  Observer.ObserverMatrix3 SSP.SSPTrit ->
  Fabric.Ternary27Point
observerRowB matrix =
  Fabric.ternary27Point
    (Observer.bA matrix)
    (Observer.bB matrix)
    (Observer.bC matrix)

observerRowC :
  Observer.ObserverMatrix3 SSP.SSPTrit ->
  Fabric.Ternary27Point
observerRowC matrix =
  Fabric.ternary27Point
    (Observer.cA matrix)
    (Observer.cB matrix)
    (Observer.cC matrix)

observerToFabric :
  Observer.ObserverMatrix3 SSP.SSPTrit ->
  Fabric.TernaryHyperformalPoint
observerToFabric matrix =
  Fabric.ternaryHyperformalPoint
    (observerRowA matrix)
    (observerRowB matrix)
    (observerRowC matrix)

fabricToObserver :
  Fabric.TernaryHyperformalPoint ->
  Observer.ObserverMatrix3 SSP.SSPTrit
fabricToObserver
  (Fabric.ternaryHyperformalPoint
    (Fabric.ternary27Point aa ab ac)
    (Fabric.ternary27Point ba bb bc)
    (Fabric.ternary27Point ca cb cc)) =
  Observer.observerMatrix3
    aa ab ac
    ba bb bc
    ca cb cc

observerFabricRoundTrip :
  (matrix : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  fabricToObserver (observerToFabric matrix) ≡ matrix
observerFabricRoundTrip
  (Observer.observerMatrix3
    aa ab ac ba bb bc ca cb cc) = refl

fabricObserverRoundTrip :
  (fabric : Fabric.TernaryHyperformalPoint) ->
  observerToFabric (fabricToObserver fabric) ≡ fabric
fabricObserverRoundTrip
  (Fabric.ternaryHyperformalPoint
    (Fabric.ternary27Point aa ab ac)
    (Fabric.ternary27Point ba bb bc)
    (Fabric.ternary27Point ca cb cc)) = refl

------------------------------------------------------------------------
-- 2. Literal flat T^9 chart.
------------------------------------------------------------------------

observerToNineTrits :
  Observer.ObserverMatrix3 SSP.SSPTrit ->
  Nine.NineTrits
observerToNineTrits
  (Observer.observerMatrix3
    aa ab ac ba bb bc ca cb cc) =
  Nine.nineTrits
    aa ab ac
    ba bb bc
    ca cb cc

nineTritsToObserver :
  Nine.NineTrits ->
  Observer.ObserverMatrix3 SSP.SSPTrit
nineTritsToObserver
  (Nine.nineTrits
    aa ab ac ba bb bc ca cb cc) =
  Observer.observerMatrix3
    aa ab ac
    ba bb bc
    ca cb cc

observerNineRoundTrip :
  (matrix : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  nineTritsToObserver (observerToNineTrits matrix) ≡ matrix
observerNineRoundTrip
  (Observer.observerMatrix3
    aa ab ac ba bb bc ca cb cc) = refl

nineObserverRoundTrip :
  (coordinates : Nine.NineTrits) ->
  observerToNineTrits (nineTritsToObserver coordinates) ≡ coordinates
nineObserverRoundTrip
  (Nine.nineTrits
    aa ab ac ba bb bc ca cb cc) = refl

observerFabricFlatChartCommutes :
  (matrix : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  Fabric.fabricToNineTrits (observerToFabric matrix)
  ≡ observerToNineTrits matrix
observerFabricFlatChartCommutes
  (Observer.observerMatrix3
    aa ab ac ba bb bc ca cb cc) = refl

------------------------------------------------------------------------
-- 3. Vec Trit 9 chart used by the canonical agreement ultrametric.
------------------------------------------------------------------------

observerToTritVec9 :
  Observer.ObserverMatrix3 SSP.SSPTrit ->
  Vec Trit.Trit 9
observerToTritVec9
  (Observer.observerMatrix3
    aa ab ac ba bb bc ca cb cc) =
  SSP.toTrit aa
  ∷ SSP.toTrit ab
  ∷ SSP.toTrit ac
  ∷ SSP.toTrit ba
  ∷ SSP.toTrit bb
  ∷ SSP.toTrit bc
  ∷ SSP.toTrit ca
  ∷ SSP.toTrit cb
  ∷ SSP.toTrit cc
  ∷ []

tritVec9ToObserver :
  Vec Trit.Trit 9 ->
  Observer.ObserverMatrix3 SSP.SSPTrit
tritVec9ToObserver
  (aa ∷ ab ∷ ac
      ∷ ba ∷ bb ∷ bc
      ∷ ca ∷ cb ∷ cc
      ∷ []) =
  Observer.observerMatrix3
    (SSP.fromTrit aa)
    (SSP.fromTrit ab)
    (SSP.fromTrit ac)
    (SSP.fromTrit ba)
    (SSP.fromTrit bb)
    (SSP.fromTrit bc)
    (SSP.fromTrit ca)
    (SSP.fromTrit cb)
    (SSP.fromTrit cc)

observerVecRoundTrip :
  (matrix : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  tritVec9ToObserver (observerToTritVec9 matrix) ≡ matrix
observerVecRoundTrip
  (Observer.observerMatrix3
    SSP.sspNegOne ab ac ba bb bc ca cb cc)
  rewrite SSP.fromTrit-toTrit ab
        | SSP.fromTrit-toTrit ac
        | SSP.fromTrit-toTrit ba
        | SSP.fromTrit-toTrit bb
        | SSP.fromTrit-toTrit bc
        | SSP.fromTrit-toTrit ca
        | SSP.fromTrit-toTrit cb
        | SSP.fromTrit-toTrit cc = refl
observerVecRoundTrip
  (Observer.observerMatrix3
    SSP.sspZero ab ac ba bb bc ca cb cc)
  rewrite SSP.fromTrit-toTrit ab
        | SSP.fromTrit-toTrit ac
        | SSP.fromTrit-toTrit ba
        | SSP.fromTrit-toTrit bb
        | SSP.fromTrit-toTrit bc
        | SSP.fromTrit-toTrit ca
        | SSP.fromTrit-toTrit cb
        | SSP.fromTrit-toTrit cc = refl
observerVecRoundTrip
  (Observer.observerMatrix3
    SSP.sspPosOne ab ac ba bb bc ca cb cc)
  rewrite SSP.fromTrit-toTrit ab
        | SSP.fromTrit-toTrit ac
        | SSP.fromTrit-toTrit ba
        | SSP.fromTrit-toTrit bb
        | SSP.fromTrit-toTrit bc
        | SSP.fromTrit-toTrit ca
        | SSP.fromTrit-toTrit cb
        | SSP.fromTrit-toTrit cc = refl

vecObserverRoundTrip :
  (coordinates : Vec Trit.Trit 9) ->
  observerToTritVec9 (tritVec9ToObserver coordinates) ≡ coordinates
vecObserverRoundTrip
  (aa ∷ ab ∷ ac
      ∷ ba ∷ bb ∷ bc
      ∷ ca ∷ cb ∷ cc
      ∷ [])
  rewrite SSP.toTrit-fromTrit aa
        | SSP.toTrit-fromTrit ab
        | SSP.toTrit-fromTrit ac
        | SSP.toTrit-fromTrit ba
        | SSP.toTrit-fromTrit bb
        | SSP.toTrit-fromTrit bc
        | SSP.toTrit-fromTrit ca
        | SSP.toTrit-fromTrit cb
        | SSP.toTrit-fromTrit cc = refl

------------------------------------------------------------------------
-- 4. Transport the exact prefix ultrametric.
------------------------------------------------------------------------

trialecticAgreementDepth :
  Observer.ObserverMatrix3 SSP.SSPTrit ->
  Observer.ObserverMatrix3 SSP.SSPTrit ->
  Nat
trialecticAgreementDepth left right =
  Metric.agreeDepth
    (observerToTritVec9 left)
    (observerToTritVec9 right)

trialecticDistance :
  Observer.ObserverMatrix3 SSP.SSPTrit ->
  Observer.ObserverMatrix3 SSP.SSPTrit ->
  Nat
trialecticDistance left right =
  Metric.dNat
    (observerToTritVec9 left)
    (observerToTritVec9 right)

trialecticStrongTriangle :
  (x y z : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  trialecticDistance x z
  ≤
  (trialecticDistance x y ⊔ trialecticDistance y z)
trialecticStrongTriangle x y z =
  Metric.ultraNat
    (observerToTritVec9 x)
    (observerToTritVec9 y)
    (observerToTritVec9 z)

trialecticStrictLegEquality :
  (x y z : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  trialecticDistance x y < trialecticDistance y z ->
  trialecticDistance x z ≡ trialecticDistance y z
trialecticStrictLegEquality x y z =
  Metric.strictLegForcesLongSideEquality
    (observerToTritVec9 x)
    (observerToTritVec9 y)
    (observerToTritVec9 z)

------------------------------------------------------------------------
-- 5. Internal participant-row ultrametric triangle.
--
-- Each participant row is one literal T^3 / 27-state hypervoxel.  Therefore
-- the A/B/C rows inside a *single* observer matrix inherit the same prefix
-- ultrametric.  This is the exact internal triangle requested by the
-- trialectic construction.
------------------------------------------------------------------------

rowToTritVec3 :
  Fabric.Ternary27Point ->
  Vec Trit.Trit 3
rowToTritVec3 (Fabric.ternary27Point x y z) =
  SSP.toTrit x ∷ SSP.toTrit y ∷ SSP.toTrit z ∷ []

participantRow :
  Observer.ObserverMatrix3 SSP.SSPTrit ->
  Observer.Participant3 ->
  Fabric.Ternary27Point
participantRow matrix Observer.participantA = observerRowA matrix
participantRow matrix Observer.participantB = observerRowB matrix
participantRow matrix Observer.participantC = observerRowC matrix

participantDistance :
  Observer.ObserverMatrix3 SSP.SSPTrit ->
  Observer.Participant3 ->
  Observer.Participant3 ->
  Nat
participantDistance matrix left right =
  Metric.dNat
    (rowToTritVec3 (participantRow matrix left))
    (rowToTritVec3 (participantRow matrix right))

participantTriangleStrong :
  (matrix : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  participantDistance matrix Observer.participantA Observer.participantC
  ≤
  ( participantDistance matrix Observer.participantA Observer.participantB
    ⊔
    participantDistance matrix Observer.participantB Observer.participantC
  )
participantTriangleStrong matrix =
  Metric.ultraNat
    (rowToTritVec3 (observerRowA matrix))
    (rowToTritVec3 (observerRowB matrix))
    (rowToTritVec3 (observerRowC matrix))

participantTriangleStrictLegEquality :
  (matrix : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  participantDistance matrix Observer.participantA Observer.participantB
  <
  participantDistance matrix Observer.participantB Observer.participantC
  ->
  participantDistance matrix Observer.participantA Observer.participantC
  ≡
  participantDistance matrix Observer.participantB Observer.participantC
participantTriangleStrictLegEquality matrix =
  Metric.strictLegForcesLongSideEquality
    (rowToTritVec3 (observerRowA matrix))
    (rowToTritVec3 (observerRowB matrix))
    (rowToTritVec3 (observerRowC matrix))

participantTriangleCyclicStrong :
  (matrix : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  participantDistance matrix Observer.participantB Observer.participantA
  ≤
  ( participantDistance matrix Observer.participantB Observer.participantC
    ⊔
    participantDistance matrix Observer.participantC Observer.participantA
  )
participantTriangleCyclicStrong matrix =
  Metric.ultraNat
    (rowToTritVec3 (observerRowB matrix))
    (rowToTritVec3 (observerRowC matrix))
    (rowToTritVec3 (observerRowA matrix))

------------------------------------------------------------------------
-- 5. Exact finite hierarchy.
------------------------------------------------------------------------

trialecticRowStateCount : Nat
trialecticRowStateCount = Fabric.hypervoxelStateCount

trialecticRowStateCountIs27 :
  trialecticRowStateCount ≡ 27
trialecticRowStateCountIs27 =
  Fabric.hypervoxelStateCountIs27

trialecticFabricStateCount : Nat
trialecticFabricStateCount = Fabric.hyperfabricStateCount

trialecticFabricStateCountIs19683 :
  trialecticFabricStateCount ≡ 19683
trialecticFabricStateCountIs19683 =
  Fabric.hyperfabricStateCountIs19683

------------------------------------------------------------------------
-- 6. Semantic / metric firewall.
------------------------------------------------------------------------

data ExactCarrierBijectionCreatesSemanticIdentity : Set where
data PrefixMetricIsPsychologicalDistance : Set where
data UltrametricEqualityCreatesCausalTrialecticLaw : Set where
data ThreeRowsDetermineTriadicFace : Set where

exactCarrierBijectionDoesNotCreateSemanticIdentity :
  ExactCarrierBijectionCreatesSemanticIdentity -> ⊥
exactCarrierBijectionDoesNotCreateSemanticIdentity ()

prefixMetricDoesNotPromoteToPsychologicalDistance :
  PrefixMetricIsPsychologicalDistance -> ⊥
prefixMetricDoesNotPromoteToPsychologicalDistance ()

ultrametricEqualityDoesNotCreateCausalTrialecticLaw :
  UltrametricEqualityCreatesCausalTrialecticLaw -> ⊥
ultrametricEqualityDoesNotCreateCausalTrialecticLaw ()

threeRowsDoNotBecomeTriadicFace :
  ThreeRowsDetermineTriadicFace -> ⊥
threeRowsDoNotBecomeTriadicFace ()

record Trialectic369HypervoxelUltrametricBoundary : Set where
  constructor trialectic-369-hypervoxel-ultrametric-boundary
  field
    observerMatrixToT9Exact : Bool
    observerMatrixToThreeCubeFabricExact : Bool
    eachObserverRowHasTwentySevenStates : Bool
    wholeObserverFabricHas19683States : Bool
    strongTriangleInequalityTransported : Bool
    strictLegEqualityTransported : Bool
    internalParticipantTriangleStrong : Bool
    internalParticipantStrictLegEquality : Bool
    exactCarrierBijectionCreatesSemanticIdentity : Bool
    prefixMetricClaimedAsPsychologicalDistance : Bool
    triadicFaceRecoveredFromRows : Bool

canonicalTrialectic369HypervoxelUltrametricBoundary :
  Trialectic369HypervoxelUltrametricBoundary
canonicalTrialectic369HypervoxelUltrametricBoundary =
  trialectic-369-hypervoxel-ultrametric-boundary
    true true true true true true true true
    false false false
