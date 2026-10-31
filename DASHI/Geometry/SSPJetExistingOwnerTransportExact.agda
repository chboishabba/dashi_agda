{-# OPTIONS --safe #-}
module DASHI.Geometry.SSPJetExistingOwnerTransportExact where

-- Canonical import seam between existing SSP ultrametric histories,
-- admissibility jet-depth rows and the downstream history consumers.
-- Deliberately NOT a second jet algebra or a claim that SSP15's 10-jet
-- rank experiment is already Agda-kernel verified.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
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
