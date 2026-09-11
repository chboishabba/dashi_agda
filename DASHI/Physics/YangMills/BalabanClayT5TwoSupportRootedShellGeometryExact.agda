{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5TwoSupportRootedShellGeometryExact where

------------------------------------------------------------------------
-- TWO-SUPPORT ROOTED-SHELL GEOMETRY
--
-- This owner isolates the representation/geometry part of the Step-V
-- connected-correlation producer from the genuinely quantitative weight-sum
-- theorem.
--
-- A cluster contributing to a two-marked connected response must contain one
-- block in support(A) and one block in support(B).  Once that same-object
-- witness is supplied, the existing physical cluster diameter and canonical
-- rooted trace give the shell coordinate.  No cluster-weight estimate is
-- proved here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalRootedShellInjectionExact as Shell

record TwoSupportGeometry
    (Block Observable : Set) : Set₁ where
  field
    distance : Block → Block → Nat
    support : Observable → Block → Set
    supportSeparation : Observable → Observable → Nat

    supportSeparationLowerBound :
      ∀ A B left right →
      support A left →
      support B right → Set

open TwoSupportGeometry public

record TwoSupportConnectingWitness
    {Block Observable Polymer Cluster : Set}
    (geometry : TwoSupportGeometry Block Observable)
    (carrier : Shell.PhysicalClusterCarrier Block Polymer Cluster)
    (A B : Observable) (cluster : Cluster) : Set₁ where
  field
    leftBlock rightBlock : Block
    leftInSupport : support geometry A leftBlock
    rightInSupport : support geometry B rightBlock
    leftInCluster :
      Shell.belongs carrier leftBlock (Shell.polymerOf carrier cluster)
    rightInCluster :
      Shell.belongs carrier rightBlock (Shell.polymerOf carrier cluster)

open TwoSupportConnectingWitness public

record TwoSupportDiameterAuthority
    {Block Observable Polymer Cluster : Set}
    (geometry : TwoSupportGeometry Block Observable)
    (carrier : Shell.PhysicalClusterCarrier Block Polymer Cluster) : Set₁ where
  field
    pairDistanceLowerBoundsSeparation :
      ∀ A B cluster →
      (witness : TwoSupportConnectingWitness geometry carrier A B cluster) →
      Set

    clusterDiameterDominatesWitnessDistance :
      ∀ A B cluster →
      (witness : TwoSupportConnectingWitness geometry carrier A B cluster) →
      Set

    connectingClusterDiameterAtLeastSeparation :
      ∀ A B cluster →
      TwoSupportConnectingWitness geometry carrier A B cluster → Set

open TwoSupportDiameterAuthority public

record TwoSupportRootedShellInjection
    {Block Observable Polymer Cluster : Set}
    (geometry : TwoSupportGeometry Block Observable)
    (carrier : Shell.PhysicalClusterCarrier Block Polymer Cluster)
    (trace : Shell.CanonicalRootedTrace Block Polymer)
    (diameter : TwoSupportDiameterAuthority geometry carrier) : Set₁ where
  field
    clusterTraceRoot : Cluster → Block
    clusterTraceWord : Cluster → List Shell.SignedAxis4
    clusterShellIndex : Cluster → Nat

    clusterTraceUsesPolymerRoot : ∀ cluster →
      clusterTraceRoot cluster ≡ Shell.root trace (Shell.polymerOf carrier cluster)
    clusterTraceUsesPolymerWord : ∀ cluster →
      clusterTraceWord cluster ≡ Shell.word trace (Shell.polymerOf carrier cluster)
    clusterShellUsesPolymerShell : ∀ cluster →
      clusterShellIndex cluster ≡ Shell.shellIndex trace (Shell.polymerOf carrier cluster)

    shellIndexAtLeastDiameter : ∀ cluster → Set

    connectingClusterRootedShellInjection :
      ∀ A B cluster →
      TwoSupportConnectingWitness geometry carrier A B cluster → Set

open TwoSupportRootedShellInjection public

------------------------------------------------------------------------
-- Proof-search boundary.
------------------------------------------------------------------------

twoSupportGeometryIsClusterWeightEstimate : Bool
twoSupportGeometryIsClusterWeightEstimate = false

rootedTraceDecoderNeedsReproof : Bool
rootedTraceDecoderNeedsReproof = false

connectingClusterGeometrySeparateFromWeightSum : Bool
connectingClusterGeometrySeparateFromWeightSum = true

absoluteConnectingWeightTailStillAnalytic : Bool
absoluteConnectingWeightTailStillAnalytic = true

clayPromotion : Bool
clayPromotion = false

twoSupportGeometryIsClusterWeightEstimateIsFalse :
  twoSupportGeometryIsClusterWeightEstimate ≡ false
twoSupportGeometryIsClusterWeightEstimateIsFalse = refl

rootedTraceDecoderNeedsReproofIsFalse : rootedTraceDecoderNeedsReproof ≡ false
rootedTraceDecoderNeedsReproofIsFalse = refl

connectingClusterGeometrySeparateFromWeightSumIsTrue :
  connectingClusterGeometrySeparateFromWeightSum ≡ true
connectingClusterGeometrySeparateFromWeightSumIsTrue = refl

absoluteConnectingWeightTailStillAnalyticIsTrue :
  absoluteConnectingWeightTailStillAnalytic ≡ true
absoluteConnectingWeightTailStillAnalyticIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl

twoSupportRootedShellGeometryLevel : ProofLevel
twoSupportRootedShellGeometryLevel = machineChecked

twoSupportPhysicalWitnessLevel : ProofLevel
twoSupportPhysicalWitnessLevel = conditional

twoSupportConnectingWeightTailLevel : ProofLevel
twoSupportConnectingWeightTailLevel = conditional
