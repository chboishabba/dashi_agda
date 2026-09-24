{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanWilsonWEXTMaxCutRound494Exact where

------------------------------------------------------------------------
-- ROUND494 / WEXT MAX-CUT: TWO-MARK WILSON EXPANSION + ROOTED WEIGHT TAIL
--
-- R491 correctly identifies the missing physical theorem as the Wilson-loop
-- two-insertion connected-shell estimate.  The generic two-mark cluster owner
-- shows that this final inequality is not primitive.  Split it into:
--
--   W1 exact connected Wilson covariance = signed contributing-cluster sum;
--   W2 finite rational triangle transport (standard/compiler analysis);
--   W3 absolute connecting-cluster weight sum <= the EXISTING traversal shell.
--
-- W3 is the genuine new quantitative Wilson extension.  No printed-J =
-- Wilson-observable identification is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; ∣_∣; _≤_)
open import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanClayT5TwoMarkedConnectedClusterTailExact as TwoMark
import DASHI.Physics.YangMills.BalabanWilsonTwoInsertionConnectedShellRound491Exact as R491

record WilsonTwoMarkWEXTSource
    (Scale Volume Root State Observable Cluster : Set) : Set₁ where
  field
    shellData : Shell.TraversalShellData Scale Volume Root

    stateAtScale : Nat → State
    scaleOf : State → Scale
    volumeOf : State → Volume

    physicalDistance : Observable → Observable → Nat
    connectingRoot : State → Observable → Observable → Root

    contributingClusters :
      State → Observable → Observable → List Cluster

    clusterWeight :
      State → Observable → Observable → Cluster → ℚ

    connectedCovariance :
      State → Observable → Observable → ℚ

    -- W1: literal Wilson two-insertion expansion on the SAME finite state.
    connectedCovarianceExpansionExact :
      ∀ state left right →
      connectedCovariance state left right
      ≡
      TwoMark.sumℚ
        (TwoMark.map
          (clusterWeight state left right)
          (contributingClusters state left right))

    -- Standard finite triangle transport.  Kept typed separately so it cannot
    -- be mistaken for the physical Wilson extension theorem.
    finiteTriangle :
      ∀ state left right →
      ∣ TwoMark.sumℚ
          (TwoMark.map
            (clusterWeight state left right)
            (contributingClusters state left right)) ∣
      ≤
      TwoMark.sumℚ
        (TwoMark.map
          (λ cluster → ∣ clusterWeight state left right cluster ∣)
          (contributingClusters state left right))

    -- Exact physical two-support meaning for the selected connected clusters.
    ConnectingClusterMeetsBothSupports :
      State → Observable → Observable → Set

    -- W3: genuine quantitative Wilson-extension payment.
    absoluteConnectingWeightSumBelowRootedShell :
      ∀ state left right →
      TwoMark.sumℚ
        (TwoMark.map
          (λ cluster → ∣ clusterWeight state left right cluster ∣)
          (contributingClusters state left right))
      ≤
      Shell.rootedShell shellData
        (scaleOf state)
        (volumeOf state)
        (connectingRoot state left right)
        (physicalDistance left right)

open WilsonTwoMarkWEXTSource public

wilsonConnectedCovarianceBelowRootedShell :
  ∀ {Scale Volume Root State Observable Cluster}
    (source :
      WilsonTwoMarkWEXTSource
        Scale Volume Root State Observable Cluster)
    state left right →
  ∣ connectedCovariance source state left right ∣
  ≤
  Shell.rootedShell (shellData source)
    (scaleOf source state)
    (volumeOf source state)
    (connectingRoot source state left right)
    (physicalDistance source left right)
wilsonConnectedCovarianceBelowRootedShell source state left right =
  ℚP.≤-trans
    (subst
      (λ value →
        ∣ value ∣
        ≤
        TwoMark.sumℚ
          (TwoMark.map
            (λ cluster →
              ∣ clusterWeight source state left right cluster ∣)
            (contributingClusters source state left right)))
      (sym (connectedCovarianceExpansionExact source state left right))
      (finiteTriangle source state left right))
    (absoluteConnectingWeightSumBelowRootedShell
      source state left right)

asWilsonTwoInsertionConnectedShell :
  ∀ {Scale Volume Root State Observable Cluster} →
  WilsonTwoMarkWEXTSource
    Scale Volume Root State Observable Cluster →
  R491.WilsonTwoInsertionConnectedShell
    Scale Volume Root State Observable
asWilsonTwoInsertionConnectedShell source = record
  { R491.WilsonTwoInsertionConnectedShell.shellData =
      shellData source
  ; R491.WilsonTwoInsertionConnectedShell.stateAtScale =
      stateAtScale source
  ; R491.WilsonTwoInsertionConnectedShell.scaleOf =
      scaleOf source
  ; R491.WilsonTwoInsertionConnectedShell.volumeOf =
      volumeOf source
  ; R491.WilsonTwoInsertionConnectedShell.physicalDistance =
      physicalDistance source
  ; R491.WilsonTwoInsertionConnectedShell.connectingRoot =
      connectingRoot source
  ; R491.WilsonTwoInsertionConnectedShell.connectedCovarianceMagnitude =
      λ state left right →
        ∣ connectedCovariance source state left right ∣
  ; R491.WilsonTwoInsertionConnectedShell.wilsonConnectedCovarianceBelowConnectingShell =
      wilsonConnectedCovarianceBelowRootedShell source
  ; R491.WilsonTwoInsertionConnectedShell.connectingClusterMeetsBothWilsonSupports =
      ConnectingClusterMeetsBothSupports source
  }

finalWEXTInequalityStoredAsPrimitive : Bool
finalWEXTInequalityStoredAsPrimitive = false

printedJEqualsWilsonObservableRequired : Bool
printedJEqualsWilsonObservableRequired = false

twoMarkExpansionStillPhysical : Bool
twoMarkExpansionStillPhysical = true

absoluteConnectingWeightTailStillPhysical : Bool
absoluteConnectingWeightTailStillPhysical = true

round494WEXTCompilerLevel : ProofLevel
round494WEXTCompilerLevel = machineChecked

round494FiniteTriangleLevel : ProofLevel
round494FiniteTriangleLevel = standardImported

literalRound494WilsonTwoMarkExpansionLevel : ProofLevel
literalRound494WilsonTwoMarkExpansionLevel = conditional

literalRound494WilsonConnectingWeightTailLevel : ProofLevel
literalRound494WilsonConnectingWeightTailLevel = conditional
