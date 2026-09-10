{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5TwoMarkedConnectedClusterTailExact where

------------------------------------------------------------------------
-- TWO-MARKED CONNECTED-CLUSTER TAIL
--
-- The existing configured T5 boundary lane already has the useful geometry:
-- a contributing boundary-crossing cluster must have diameter at least the
-- observable-to-boundary distance, is injected into a rooted shell, and the
-- shell weight is bounded by the canonical configured tail.
--
-- Connected two-point clustering needs the same compiler shape, with a
-- different event:
--
--   cluster crosses observable support -> boundary
--
-- becomes
--
--   cluster connects support(A) -> support(B).
--
-- This module deliberately does NOT manufacture that physical event or its
-- expansion.  It makes the first theorem-bearing Step-V leaf explicit and
-- reuses the already-owned numerical tail once the same-carrier two-mark
-- support/geometry receipts are supplied.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational using (ℚ; _≤_)

import DASHI.Physics.YangMills.BalabanClayT5ConfiguredGeometricTailExact as Tail

record TwoMarkedConnectedClusterTail
    (Cutoff Observable Cluster : Set) : Set₁ where
  field
    supportSeparation : Observable → Observable → Nat
    clusterDiameter : Cluster → Nat
    clusterWeight : Cutoff → Observable → Observable → Cluster → ℚ

    contributesToConnectedResponse :
      Cutoff → Observable → Observable → Cluster → Set

    -- SAME-OBJECT / REPRESENTATION LEAF:
    -- only clusters that genuinely connect the two marked supports survive in
    -- the connected response expansion.
    contributingClusterConnectsBothSupports :
      ∀ cutoff A B cluster →
      contributesToConnectedResponse cutoff A B cluster → Set

    -- GEOMETRY LEAF:
    -- a cluster joining both supports has enough diameter to span their
    -- separation.  Kept as a physical input rather than borrowed from the
    -- postulated generic GraphCombinatorics surface.
    connectingClusterDiameterAtLeastSeparation :
      ∀ cutoff A B cluster →
      contributesToConnectedResponse cutoff A B cluster → Set

    -- ENUMERATION / TAIL LEAF:
    -- the selected contributing clusters admit the same rooted-shell
    -- injection and configured shell-weight bound already used by T5 boundary
    -- cancellation.
    connectingClusterRootedShellInjection :
      ∀ cutoff A B cluster →
      contributesToConnectedResponse cutoff A B cluster → Set

    rootedShellWeightBoundAtSeparation :
      ∀ cutoff A B → Set

    connectedResponse : Cutoff → Observable → Observable → ℚ
    absoluteValue : ℚ → ℚ

    twoMarkedConnectedExpansionExact :
      ∀ cutoff A B → Set

    -- This is the first fully quantitative payment after the preceding
    -- representation/geometry leaves.  It is stated on the canonical T5 tail
    -- rather than a newly invented envelope.
    connectedResponseBelowConfiguredTail :
      ∀ cutoff A B →
      absoluteValue (connectedResponse cutoff A B)
      ≤ Tail.rootedShellTail (supportSeparation A B)

open TwoMarkedConnectedClusterTail public

connectedResponseHasConfiguredSeparationTail :
  ∀ {Cutoff Observable Cluster}
    (dataSet : TwoMarkedConnectedClusterTail Cutoff Observable Cluster)
    cutoff A B →
  absoluteValue dataSet (connectedResponse dataSet cutoff A B)
  ≤ Tail.rootedShellTail (supportSeparation dataSet A B)
connectedResponseHasConfiguredSeparationTail dataSet =
  connectedResponseBelowConfiguredTail dataSet

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

twoMarkedCarrierSeparateFromSingleMarkedMomentCarrier : Bool
twoMarkedCarrierSeparateFromSingleMarkedMomentCarrier = true

twoMarkedExpansionManufacturedByThisCompiler : Bool
twoMarkedExpansionManufacturedByThisCompiler = false

connectedClusterGeometryManufacturedByThisCompiler : Bool
connectedClusterGeometryManufacturedByThisCompiler = false

configuredRootedTailReused : Bool
configuredRootedTailReused = true

clusterWeightDecayAloneDefinitionallyImpliesConnectedResponseDecay : Bool
clusterWeightDecayAloneDefinitionallyImpliesConnectedResponseDecay = false

clayPromotion : Bool
clayPromotion = false

twoMarkedCarrierSeparateFromSingleMarkedMomentCarrierIsTrue :
  twoMarkedCarrierSeparateFromSingleMarkedMomentCarrier ≡ true
twoMarkedCarrierSeparateFromSingleMarkedMomentCarrierIsTrue = refl

twoMarkedExpansionManufacturedByThisCompilerIsFalse :
  twoMarkedExpansionManufacturedByThisCompiler ≡ false
twoMarkedExpansionManufacturedByThisCompilerIsFalse = refl

configuredRootedTailReusedIsTrue : configuredRootedTailReused ≡ true
configuredRootedTailReusedIsTrue = refl

clusterWeightDecayAloneDefinitionallyImpliesConnectedResponseDecayIsFalse :
  clusterWeightDecayAloneDefinitionallyImpliesConnectedResponseDecay ≡ false
clusterWeightDecayAloneDefinitionallyImpliesConnectedResponseDecayIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
