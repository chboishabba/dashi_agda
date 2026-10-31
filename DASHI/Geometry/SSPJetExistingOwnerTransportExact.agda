{-# OPTIONS --safe #-}
module DASHI.Geometry.SSPJetExistingOwnerTransportExact where

-- Canonical import seam between existing SSP ultrametric histories,
-- admissibility jet-depth rows and the downstream history consumers.
-- Deliberately NOT a second jet algebra or a claim that SSP15's 10-jet
-- rank experiment is already Agda-kernel verified.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong)
import DASHI.Geometry.SSP369Ultrametric as SSP
import DASHI.Geometry.AdmissibilityJetSpec as Jet
import DASHI.Geometry.Admissibility369UltrametricBridge as Bridge

-- The existing ultrametric owner already proves identity observations
-- preserve the full typed history address.
selfHistoryDistanceZero :
  ∀ {depth : Nat} (history : SSP.Address depth) →
  SSP.distance history history ≡ zero
selfHistoryDistanceZero = SSP.distance-self-zero

-- The concrete existing two-jet admissibility row is not a new theorem
-- about physical jets. It imports the exact typed ultrametric receipt.
metricTwoJetHistoryPreserved :
  SSP.distance Bridge.metricTwoJetAddress
               Bridge.metricTwoJetAddress ≡ zero
metricTwoJetHistoryPreserved =
  Bridge.metricRowUsesExistingUltrametricSelfDistance

-- The original jet order is retained in its source row.
metricTwoJetOrderIsDepth :
  Jet.jetOrder (Bridge.admissibilitySpec Bridge.metricTwoJetUltrametricRow)
  ≡ Jet.addressDepth Bridge.metricTwoJetUltrametricRow
metricTwoJetOrderIsDepth =
  Jet.jetOrderMatchesAddressDepth Bridge.metricTwoJetUltrametricRow

-- Any consumer on a retained full SSP address respects equality of
-- actual histories; equality of truncated prefixes alone is insufficient.
retainedJetConsumerAgreement :
  ∀ {depth : Nat} {Outcome : Set}
  (consumer : SSP.Address depth → Outcome)
  (left right : SSP.Address depth) →
  left ≡ right → consumer left ≡ consumer right
retainedJetConsumerAgreement consumer left right refl = refl

-- Zero ultrametric distance is a genuine sufficient observation for
-- EVERY consumer of the original finite SSP address. A short prefix
-- (small but nonzero distance) does NOT license this conclusion.
zeroDistanceConsumerAgreement :
  ∀ {depth : Nat} {Outcome : Set}
  (consumer : SSP.Address depth → Outcome)
  (left right : SSP.Address depth) →
  SSP.distance left right ≡ zero →
  consumer left ≡ consumer right
zeroDistanceConsumerAgreement consumer left right d0 =
  cong consumer (SSP.distance-zero→equal left right d0)

-- Conversely, whenever a specific consumer distinguishes two addresses,
-- those full histories cannot be at zero ultrametric distance.
consumerDifferenceForcesPositiveResolution :
  ∀ {depth : Nat} {Outcome : Set}
  (consumer : SSP.Address depth → Outcome)
  (left right : SSP.Address depth) →
  (consumer left ≡ consumer right → ⊥) →
  SSP.distance left right ≡ zero → ⊥
consumerDifferenceForcesPositiveResolution consumer left right different d0 =
  different (zeroDistanceConsumerAgreement consumer left right d0)

-- Consumer-indexed version of the existing full-depth zero-distance law.
-- This is a nontrivial observer theorem because the hypothesis concerns
-- observable distance rather than definitional equality of consumers.
import DASHI.Core.ConsumerIndexedResidualRefinementExact as Residual

ultrametricZeroSufficient :
  ∀ {depth : Nat} {Outcome : Set}
  (consumer : SSP.Address depth → Outcome) →
  (x y : SSP.Address depth) →
  SSP.distance x y ≡ zero → consumer x ≡ consumer y
ultrametricZeroSufficient = zeroDistanceConsumerAgreement

-- A *supplied* observation map, not a conflation of arbitrary producer
-- types with SSP addresses. It must separate all original histories.
record FaithfulSSPAddress
    (History : Set) (depth : Nat) : Set₁ where
  field
    encode : History → SSP.Address depth
    faithful : ∀ x y → encode x ≡ encode y → x ≡ y
open FaithfulSSPAddress public

faithfulAddressConsumerSufficient :
  ∀ {History Outcome : Set} {depth : Nat}
  (address : FaithfulSSPAddress History depth)
  (consumer : History → Outcome) →
  Residual.ConsumerSufficient (encode address) consumer
faithfulAddressConsumerSufficient address consumer x y same =
  cong consumer (faithful address x y same)

-- A collision on an insufficient coarse observer is *forced* to differ
-- on any sufficiently faithful SSP ultrametric address.
coarseCollisionRequiresAddressDistinction :
  ∀ {History Coarse Outcome : Set} {depth : Nat}
  {coarse : History → Coarse}
  {consumer : History → Outcome}
  (collision : Residual.ConsumerRelevantCollision coarse consumer)
  (address : FaithfulSSPAddress History depth) →
  encode address (Residual.left collision) ≡
  encode address (Residual.right collision) → ⊥
coarseCollisionRequiresAddressDistinction collision address =
  Residual.everySufficientObserverSeparatesRelevantCollision
    collision (faithfulAddressConsumerSufficient address consumer)
