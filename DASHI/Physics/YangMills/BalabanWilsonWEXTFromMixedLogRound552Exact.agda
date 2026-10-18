{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanWilsonWEXTFromMixedLogRound552Exact where

------------------------------------------------------------------------
-- GOAL-1 B-WEXT / ROUND552:
-- CONSTRUCT R494 FROM THE SOURCE-CORRECT W1 + THE GENUINE W3 TAIL
--
-- W1 is supplied only as R551's literal Wilson mixed-log cluster expansion.
-- The connected-covariance presentation consumed by R494 is compiler output.
--
-- The remaining independent quantitative payment is W3:
--
--   absolute connecting-cluster weight sum <= rooted shell.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; ∣_∣; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanClayT5TwoMarkedConnectedClusterTailExact as TwoMark
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanWilsonMixedLogClusterExpansionRound551Exact as R551
import DASHI.Physics.YangMills.BalabanWilsonWEXTMaxCutRound494Exact as R494

record WilsonWEXTFromMixedLogSource
    (Scale Volume Root State Observable SourceDirection Cluster : Set) : Set₁ where
  field
    expansion :
      R551.WilsonMixedLogClusterExpansionSource
        State Observable SourceDirection Cluster

    shellData :
      Shell.TraversalShellData Scale Volume Root

    stateAtScale : Nat → State
    scaleOf : State → Scale
    volumeOf : State → Volume

    physicalDistance : Observable → Observable → Nat
    connectingRoot : State → Observable → Observable → Root

    ConnectingClusterMeetsBothSupports :
      State → Observable → Observable → Set

    absoluteConnectingWeightSumBelowRootedShell :
      ∀ state left right →
      TwoMark.sumℚ
        (TwoMark.map
          (λ cluster →
            ∣ R551.clusterWeight expansion state left right cluster ∣)
          (R551.contributingClusters expansion state left right))
      ≤
      Shell.rootedShell shellData
        (scaleOf state)
        (volumeOf state)
        (connectingRoot state left right)
        (physicalDistance left right)

open WilsonWEXTFromMixedLogSource public

asR494 :
  ∀ {Scale Volume Root State Observable SourceDirection Cluster} →
  WilsonWEXTFromMixedLogSource
    Scale Volume Root State Observable SourceDirection Cluster →
  R494.WilsonTwoMarkWEXTSource
    Scale Volume Root State Observable Cluster
asR494 source = record
  { R494.WilsonTwoMarkWEXTSource.shellData =
      shellData source
  ; R494.WilsonTwoMarkWEXTSource.stateAtScale =
      stateAtScale source
  ; R494.WilsonTwoMarkWEXTSource.scaleOf =
      scaleOf source
  ; R494.WilsonTwoMarkWEXTSource.volumeOf =
      volumeOf source
  ; R494.WilsonTwoMarkWEXTSource.physicalDistance =
      physicalDistance source
  ; R494.WilsonTwoMarkWEXTSource.connectingRoot =
      connectingRoot source
  ; R494.WilsonTwoMarkWEXTSource.contributingClusters =
      R551.contributingClusters (expansion source)
  ; R494.WilsonTwoMarkWEXTSource.clusterWeight =
      R551.clusterWeight (expansion source)
  ; R494.WilsonTwoMarkWEXTSource.connectedCovariance =
      λ state left right →
        Cumulant.connectedCovariance
          (R551.momentAlgebra (expansion source) state)
          left right
  ; R494.WilsonTwoMarkWEXTSource.connectedCovarianceExpansionExact =
      R551.connectedCovarianceExpansionExact (expansion source)
  ; R494.WilsonTwoMarkWEXTSource.ConnectingClusterMeetsBothSupports =
      ConnectingClusterMeetsBothSupports source
  ; R494.WilsonTwoMarkWEXTSource.absoluteConnectingWeightSumBelowRootedShell =
      absoluteConnectingWeightSumBelowRootedShell source
  }

round552WEXTAdapterCompilerLevel : ProofLevel
round552WEXTAdapterCompilerLevel = machineChecked

round552IndependentCovarianceExpansionFieldRequired : Bool
round552IndependentCovarianceExpansionFieldRequired = false

literalRound552WilsonMixedLogClusterExpansionLevel : ProofLevel
literalRound552WilsonMixedLogClusterExpansionLevel =
  R551.literalRound551WilsonMixedLogClusterExpansionLevel

literalRound552ConnectingWeightTailLevel : ProofLevel
literalRound552ConnectingWeightTailLevel =
  R494.literalRound494WilsonConnectingWeightTailLevel
