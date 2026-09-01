module DASHI.Computation.SSSPSortingBarrierTernaryBidiExact where

-- Source boundary:
-- Ran Duan, Jiayi Mao, Xiao Mao, Xinkai Shu, Longhui Yin,
-- "Breaking the Sorting Barrier for Directed Single-Source Shortest Paths",
-- arXiv:2504.17033v2 (2025).
--
-- This owner formalises only the representation lesson used by the algorithm:
-- SSSP need not expose a total distance ordering in order to expose exact
-- shortest-distance information.  The paper-specific 1/3 and 2/3 logarithmic
-- scales are recorded separately from the ternary carrier.  In particular,
-- this file does NOT claim that the exponent 2/3 is caused by Base369.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Relation.Nullary using (¬_)
open import Data.Vec using (Vec; []; _∷_)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos; inv)
import DASHI.Physics.RealTernaryCarrier as RTC

------------------------------------------------------------------------
-- Paper cost metadata: kept independent of the observation carrier.

record LogScaleSplit : Set where
  constructor logScaleSplit
  field
    kNumerator : Nat
    tNumerator : Nat
    denominator : Nat
    splitWhole : kNumerator + tNumerator ≡ denominator

paper2025ScaleSplit : LogScaleSplit
paper2025ScaleSplit = logScaleSplit 1 2 3 refl

paper2025-kNumerator : LogScaleSplit.kNumerator paper2025ScaleSplit ≡ 1
paper2025-kNumerator = refl

paper2025-tNumerator : LogScaleSplit.tNumerator paper2025ScaleSplit ≡ 2
paper2025-tNumerator = refl

paper2025-denominator : LogScaleSplit.denominator paper2025ScaleSplit ≡ 3
paper2025-denominator = refl

------------------------------------------------------------------------
-- Partial relative-order observation.
--
-- neg : left is required/certified before right
-- zer : relative order is deliberately not exposed to this consumer
-- pos : right is required/certified before left
--
-- The middle trit is therefore a retained residual, not an error value.

DistanceOrderObservation : Set
DistanceOrderObservation = Trit

flipDistanceOrder : DistanceOrderObservation → DistanceOrderObservation
flipDistanceOrder = inv

flip-before : flipDistanceOrder neg ≡ pos
flip-before = refl

flip-unresolved : flipDistanceOrder zer ≡ zer
flip-unresolved = refl

flip-after : flipDistanceOrder pos ≡ neg
flip-after = refl

------------------------------------------------------------------------
-- Typed 3 + 6 Base369-compatible observation geometry.
--
-- The three coarse coordinates describe the consumer-visible recursive state.
-- The six fine coordinates retain algorithmic residual information.  The names
-- are SSSP-owned; sharing T3^3 x T3^6 geometry does not make this a Monster
-- representation.

record SSSPObservation : Set where
  constructor ssspObservation
  field
    relativeDistance : Trit
    relaxationProgress : Trit
    settlementAuthority : Trit

    frontierReduction : Trit
    boundProgress : Trit
    pivotDependence : Trit
    recursiveProgress : Trit
    workloadStatus : Trit
    consumerOrderDemand : Trit

open SSSPObservation public

CoarseCarrier : Set
CoarseCarrier = RTC.Carrier 3

ResidualFibre : Set
ResidualFibre = RTC.Carrier 6

HyperfabricCarrier : Set
HyperfabricCarrier = RTC.Carrier 9

coarseCarrier : SSSPObservation → CoarseCarrier
coarseCarrier x =
  relativeDistance x ∷
  relaxationProgress x ∷
  settlementAuthority x ∷
  []

residualFibre : SSSPObservation → ResidualFibre
residualFibre x =
  frontierReduction x ∷
  boundProgress x ∷
  pivotDependence x ∷
  recursiveProgress x ∷
  workloadStatus x ∷
  consumerOrderDemand x ∷
  []

toHyperfabric : SSSPObservation → HyperfabricCarrier
toHyperfabric x =
  relativeDistance x ∷
  relaxationProgress x ∷
  settlementAuthority x ∷
  frontierReduction x ∷
  boundProgress x ∷
  pivotDependence x ∷
  recursiveProgress x ∷
  workloadStatus x ∷
  consumerOrderDemand x ∷
  []

flipObservation : SSSPObservation → SSSPObservation
flipObservation x =
  ssspObservation
    (inv (relativeDistance x))
    (inv (relaxationProgress x))
    (inv (settlementAuthority x))
    (inv (frontierReduction x))
    (inv (boundProgress x))
    (inv (pivotDependence x))
    (inv (recursiveProgress x))
    (inv (workloadStatus x))
    (inv (consumerOrderDemand x))

flipObservation-hyperfabric :
  (x : SSSPObservation) →
  toHyperfabric (flipObservation x) ≡ RTC.invVec (toHyperfabric x)
flipObservation-hyperfabric x = refl

------------------------------------------------------------------------
-- Exact finite quotient witness for the sorting-barrier idea.
--
-- Two distinct total-order witnesses can be observationally identical when a
-- consumer does not request their relative order.  This is the minimal finite
-- theorem shape behind "do not pay to totalise information the consumer does
-- not need".

data PairTotalOrder : Set where
  leftBeforeRight : PairTotalOrder
  rightBeforeLeft : PairTotalOrder

leftBeforeRight≠rightBeforeLeft :
  ¬ (leftBeforeRight ≡ rightBeforeLeft)
leftBeforeRight≠rightBeforeLeft ()

partialOrderQuotient : PairTotalOrder → DistanceOrderObservation
partialOrderQuotient leftBeforeRight = zer
partialOrderQuotient rightBeforeLeft = zer

distinct-total-orders-collapse :
  partialOrderQuotient leftBeforeRight ≡
  partialOrderQuotient rightBeforeLeft
distinct-total-orders-collapse = refl

------------------------------------------------------------------------
-- Consumer descent.
--
-- An SSSP-facing consumer can depend on exact distance output while being
-- invariant under erased pair-order information.  We keep the distance output
-- abstract here so this structural owner does not pretend to implement the
-- complete BMSSP arithmetic proof.

record OrderInsensitiveConsumer : Set₁ where
  field
    Output : Set
    consumePartial : DistanceOrderObservation → Output

open OrderInsensitiveConsumer public

consumeTotal :
  (C : OrderInsensitiveConsumer) →
  PairTotalOrder → Output C
consumeTotal C o = consumePartial C (partialOrderQuotient o)

consumer-descends-through-partial-order :
  (C : OrderInsensitiveConsumer) →
  consumeTotal C leftBeforeRight ≡ consumeTotal C rightBeforeLeft
consumer-descends-through-partial-order C = refl

------------------------------------------------------------------------
-- BIDI boundary receipts.
--
-- Forward: total-order witnesses may be projected to the partial-order surface.
-- Backward: the partial surface cannot reconstruct which total order was used.
-- The lost coordinate is retained as an explicit residual rather than silently
-- declared irrelevant for every possible consumer.

data Reconstruction : Set where
  reconstructedLeft : Reconstruction
  reconstructedRight : Reconstruction
  unresolvedOrder : Reconstruction

reconstructFromPartial : DistanceOrderObservation → Reconstruction
reconstructFromPartial neg = reconstructedLeft
reconstructFromPartial zer = unresolvedOrder
reconstructFromPartial pos = reconstructedRight

quotient-reconstruction-retains-middle :
  reconstructFromPartial (partialOrderQuotient leftBeforeRight) ≡ unresolvedOrder
quotient-reconstruction-retains-middle = refl

------------------------------------------------------------------------
-- Explicit representation firewall.
--
-- T3^3 x T3^6 = T3^9 is used here only as a typed finite observation carrier.
-- No theorem in this owner promotes SSSP state to the finite Heisenberg group,
-- Schrodinger module, Monster 729 constituent, or Monster representation.

SSSPCarrierIsNineTrits : Set
SSSPCarrierIsNineTrits = HyperfabricCarrier
