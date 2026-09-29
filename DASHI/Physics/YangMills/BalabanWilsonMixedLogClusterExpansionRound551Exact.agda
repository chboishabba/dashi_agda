{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanWilsonMixedLogClusterExpansionRound551Exact where

------------------------------------------------------------------------
-- GOAL-1 B-WEXT / ROUND551:
-- THE W1 SOURCE THEOREM IS MIXED-LOG -> CONNECTED CLUSTER SUM
--
-- Generic normalized two-source calculus already proves
--
--   D_L D_R log Z = Cov(L,R).
--
-- Therefore WEXT must not ask for a second physical theorem whose left-hand
-- side is "connected covariance" merely because that is the downstream name.
--
-- The genuine Wilson-specific extension is:
--
--   literal Wilson mixed-log response
--     = sum of the contributing connected polymer-cluster weights.
--
-- R551 compiles that source theorem to the exact covariance expansion consumed
-- by R494.  W3 (absolute connecting-weight tail <= rooted shell) remains a
-- separate physical estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanClayT5TwoMarkedConnectedClusterTailExact as TwoMark

record WilsonMixedLogClusterExpansionSource
    (State Observable SourceDirection Cluster : Set) : Set₁ where
  field
    momentAlgebra :
      State → Cumulant.TwoSourceMomentAlgebra Observable ℚ

    sourceCalculus :
      ∀ state →
      Cumulant.NormalizedLogSourceCalculus
        (momentAlgebra state)

    insertionMeaning :
      ∀ state →
      Cumulant.LiteralTwoSourceInsertionMeaning
        (sourceCalculus state)
        SourceDirection

    contributingClusters :
      State → Observable → Observable → List Cluster

    clusterWeight :
      State → Observable → Observable → Cluster → ℚ

    -- The only W1 physical theorem after generic cumulant calculus is removed.
    literalWilsonMixedLogIsConnectedClusterSum :
      ∀ state left right →
      Cumulant.literalMixedSecondLogDerivative
        (insertionMeaning state)
        (Cumulant.sourceDirectionOf (insertionMeaning state) left)
        (Cumulant.sourceDirectionOf (insertionMeaning state) right)
      ≡
      TwoMark.sumℚ
        (TwoMark.map
          (clusterWeight state left right)
          (contributingClusters state left right))

open WilsonMixedLogClusterExpansionSource public

connectedCovarianceExpansionExact :
  ∀ {State Observable SourceDirection Cluster}
    (source :
      WilsonMixedLogClusterExpansionSource
        State Observable SourceDirection Cluster)
    state left right →
  Cumulant.connectedCovariance
    (momentAlgebra source state)
    left right
  ≡
  TwoMark.sumℚ
    (TwoMark.map
      (clusterWeight source state left right)
      (contributingClusters source state left right))
connectedCovarianceExpansionExact source state left right =
  trans
    (sym
      (Cumulant.literalMixedLogDerivativeIsConnectedCovariance
        (insertionMeaning source state)
        left right))
    (literalWilsonMixedLogIsConnectedClusterSum
      source state left right)

round551CumulantToCovarianceCompilerLevel : ProofLevel
round551CumulantToCovarianceCompilerLevel =
  Cumulant.twoSourceConnectedCumulantCompilerLevel

round551WilsonCovarianceExpansionCompilerLevel : ProofLevel
round551WilsonCovarianceExpansionCompilerLevel = machineChecked

round551SecondPhysicalCovarianceIdentityRequired : Bool
round551SecondPhysicalCovarianceIdentityRequired = false

round551PrintedBalabanJEqualsWilsonObservableRequired : Bool
round551PrintedBalabanJEqualsWilsonObservableRequired = false

-- Genuine unpublished/source-extension theorem:
-- instantiate the normalized source directions by the selected Wilson pair and
-- prove their literal mixed-log derivative has the connected polymer expansion.
literalRound551WilsonMixedLogClusterExpansionLevel : ProofLevel
literalRound551WilsonMixedLogClusterExpansionLevel = conditional
