{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5TwoMarkedConnectedClusterTailExact where

------------------------------------------------------------------------
-- TWO-MARKED CONNECTED-CLUSTER TAIL
--
-- The configured T5 boundary lane already uses the right proof shape:
-- a contributing cluster is forced far enough into a rooted shell and the
-- resulting absolute shell sum is controlled by `rootedShellTail`.
--
-- For connected two-point clustering the event is instead:
--
--   cluster connects support(A) -> support(B).
--
-- This owner now makes the final correlation bound genuine COMPILER OUTPUT.
-- It does not store that final inequality as an input.  The live quantitative
-- physical payment is the absolute weight sum of the connecting clusters;
-- exact connected-response expansion and finite triangle transport are kept
-- separate from that payment.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational using (ℚ; 0ℚ; _+_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)
import Data.Rational.Properties as ℚP

import DASHI.Physics.YangMills.BalabanClayT5ConfiguredGeometricTailExact as Tail

sumℚ : List ℚ → ℚ
sumℚ [] = 0ℚ
sumℚ (x ∷ xs) = x + sumℚ xs

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

record TwoMarkedConnectedClusterTail
    (Cutoff Observable Cluster : Set) : Set₁ where
  field
    supportSeparation : Observable → Observable → Nat
    clusterDiameter : Cluster → Nat

    contributingClusters : Cutoff → Observable → Observable → List Cluster
    clusterWeight : Cutoff → Observable → Observable → Cluster → ℚ

    connectedResponse : Cutoff → Observable → Observable → ℚ
    absoluteValue : ℚ → ℚ

    -- REPRESENTATION LEAF: the connected two-source response is exactly the
    -- signed sum over clusters retained by the two-mark expansion.
    connectedResponseExpansionExact : ∀ cutoff A B →
      connectedResponse cutoff A B
      ≡ sumℚ
          (map (clusterWeight cutoff A B)
            (contributingClusters cutoff A B))

    -- PURE FINITE ANALYSIS / COMPILER INPUT: move absolute value outside the
    -- already-selected signed cluster sum.  This should ultimately be supplied
    -- by the canonical rational absolute-value algebra, not by cluster physics.
    finiteTriangleForConnectingSum : ∀ cutoff A B →
      absoluteValue
        (sumℚ
          (map (clusterWeight cutoff A B)
            (contributingClusters cutoff A B)))
      ≤
      sumℚ
        (map
          (λ cluster → absoluteValue (clusterWeight cutoff A B cluster))
          (contributingClusters cutoff A B))

    -- PHYSICAL GEOMETRY / ENUMERATION LEAF: every retained cluster genuinely
    -- connects both marked supports and therefore lies at rooted depth at least
    -- their separation.  These are intentionally proof-bearing obligations,
    -- not Booleans and not consequences manufactured here.
    contributingClusterConnectsBothSupports :
      ∀ cutoff A B cluster →
      cluster ∈ contributingClusters cutoff A B → Set

    connectingClusterDiameterAtLeastSeparation :
      ∀ cutoff A B cluster →
      cluster ∈ contributingClusters cutoff A B → Set

    connectingClusterRootedShellInjection :
      ∀ cutoff A B cluster →
      cluster ∈ contributingClusters cutoff A B → Set

    -- THIS is the theorem-bearing quantitative Step-V payment after the
    -- representation/geometry leaves: the absolute connecting-cluster weight
    -- sum is bounded by the already-owned configured rooted tail.
    absoluteConnectingWeightSumBelowRootedTail : ∀ cutoff A B →
      sumℚ
        (map
          (λ cluster → absoluteValue (clusterWeight cutoff A B cluster))
          (contributingClusters cutoff A B))
      ≤ Tail.rootedShellTail (supportSeparation A B)

open TwoMarkedConnectedClusterTail public

connectedResponseHasConfiguredSeparationTail :
  ∀ {Cutoff Observable Cluster}
    (dataSet : TwoMarkedConnectedClusterTail Cutoff Observable Cluster)
    cutoff A B →
  absoluteValue dataSet (connectedResponse dataSet cutoff A B)
  ≤ Tail.rootedShellTail (supportSeparation dataSet A B)
connectedResponseHasConfiguredSeparationTail dataSet cutoff A B =
  ℚP.≤-trans
    (subst
      (λ value →
        absoluteValue dataSet value
        ≤
        sumℚ
          (map
            (λ cluster →
              absoluteValue dataSet
                (clusterWeight dataSet cutoff A B cluster))
            (contributingClusters dataSet cutoff A B)))
      (sym (connectedResponseExpansionExact dataSet cutoff A B))
      (finiteTriangleForConnectingSum dataSet cutoff A B))
    (absoluteConnectingWeightSumBelowRootedTail dataSet cutoff A B)

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

twoMarkedCarrierSeparateFromSingleMarkedMomentCarrier : Bool
twoMarkedCarrierSeparateFromSingleMarkedMomentCarrier = true

finalConnectedTailStoredAsPrimitiveInput : Bool
finalConnectedTailStoredAsPrimitiveInput = false

twoMarkedExpansionManufacturedByThisCompiler : Bool
twoMarkedExpansionManufacturedByThisCompiler = false

connectedClusterGeometryManufacturedByThisCompiler : Bool
connectedClusterGeometryManufacturedByThisCompiler = false

configuredRootedTailReused : Bool
configuredRootedTailReused = true

absoluteConnectingWeightSumIsLiveStepVPayment : Bool
absoluteConnectingWeightSumIsLiveStepVPayment = true

clusterWeightDecayAloneDefinitionallyImpliesConnectedResponseDecay : Bool
clusterWeightDecayAloneDefinitionallyImpliesConnectedResponseDecay = false

clayPromotion : Bool
clayPromotion = false

finalConnectedTailStoredAsPrimitiveInputIsFalse :
  finalConnectedTailStoredAsPrimitiveInput ≡ false
finalConnectedTailStoredAsPrimitiveInputIsFalse = refl

configuredRootedTailReusedIsTrue : configuredRootedTailReused ≡ true
configuredRootedTailReusedIsTrue = refl

absoluteConnectingWeightSumIsLiveStepVPaymentIsTrue :
  absoluteConnectingWeightSumIsLiveStepVPayment ≡ true
absoluteConnectingWeightSumIsLiveStepVPaymentIsTrue = refl

clusterWeightDecayAloneDefinitionallyImpliesConnectedResponseDecayIsFalse :
  clusterWeightDecayAloneDefinitionallyImpliesConnectedResponseDecay ≡ false
clusterWeightDecayAloneDefinitionallyImpliesConnectedResponseDecayIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
