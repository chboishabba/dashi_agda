module DASHI.Analysis.RiemannAristotleNearFarAllowanceCompositionExact where

------------------------------------------------------------------------
-- BIDI MEETING LAYER: ACTUAL PRODUCERS + REMAINING ALLOWANCE
--
-- At one common cutoff J, the analytic work may naturally prove
--
--   B_far(J) < epsilon
--   B_near(J) + epsilon < M_cluster
--
-- rather than directly proving B_near(J)+B_far(J)<M_cluster.
-- This module performs that last scalar composition and feeds the already-owned
-- near/far closure compiler.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ; _+_; _≤_; _<_)
import Data.Rational.Properties as ℚP

import DASHI.Analysis.RiemannAristotleNearFarShellProducerSocketsExact as Socket
import DASHI.Analysis.RiemannAristotleNearFarShellCompositionExact as Compose

record NearFarAllowanceClosure : Set where
  constructor near-far-allowance-closure
  field
    near : Socket.FiniteSignedNearShellCore
    far : Socket.FarShellQuantitativeEnvelope
    compatible : Socket.CompatibleNearFarProducers near far

    offResidualSq clusterMargin allowance : ℚ

    offSplitBound :
      offResidualSq
        ≤ Socket.signedNearContribution near
          + Socket.farContribution far

    farBudgetFitsAllowance :
      Socket.farBudget far < allowance

    nearBudgetPlusAllowanceBelowCluster :
      Socket.nearBudget near + allowance < clusterMargin

open NearFarAllowanceClosure public

combinedProducerBudgetBelowCluster :
  (d : NearFarAllowanceClosure) →
  Socket.nearBudget (near d) + Socket.farBudget (far d)
    < clusterMargin d
combinedProducerBudgetBelowCluster d =
  ℚP.<-trans
    (ℚP.+-monoʳ-<
      (Socket.nearBudget (near d))
      (farBudgetFitsAllowance d))
    (nearBudgetPlusAllowanceBelowCluster d)

compiledAnalyticClosure :
  (d : NearFarAllowanceClosure) → Compose.NearFarAnalyticClosure
compiledAnalyticClosure d =
  record
    { near = near d
    ; far = far d
    ; compatible = compatible d
    ; offResidualSq = offResidualSq d
    ; clusterMargin = clusterMargin d
    ; offSplitBound = offSplitBound d
    ; combinedBudgetBelowClusterMargin = combinedProducerBudgetBelowCluster d
    }

allowanceClosureStrictlyBelowCluster :
  (d : NearFarAllowanceClosure) →
  offResidualSq d < clusterMargin d
allowanceClosureStrictlyBelowCluster d =
  Compose.analyticClosureStrictlyBelowClusterMargin
    (compiledAnalyticClosure d)

allowanceClosureContradictsExactSchur :
  (d : NearFarAllowanceClosure) →
  clusterMargin d ≡ offResidualSq d →
  ⊥
allowanceClosureContradictsExactSchur d exactSchur =
  Compose.analyticClosureContradictsExactSchur
    (compiledAnalyticClosure d)
    exactSchur

record NearFarAllowanceBoundary : Set where
  constructor near-far-allowance-boundary
  field
    allowanceCompositionClosed : Bool
    allowanceCompositionClosedIsTrue : allowanceCompositionClosed ≡ true

    allowanceMustBeatActualFarBudget : Bool
    allowanceMustBeatActualFarBudgetIsTrue :
      allowanceMustBeatActualFarBudget ≡ true

    nearBudgetMustLeaveAllowanceBelowCluster : Bool
    nearBudgetMustLeaveAllowanceBelowClusterIsTrue :
      nearBudgetMustLeaveAllowanceBelowCluster ≡ true

    compilerChoosesAnalyticCutoff : Bool
    compilerChoosesAnalyticCutoffIsFalse :
      compilerChoosesAnalyticCutoff ≡ false

canonicalNearFarAllowanceBoundary : NearFarAllowanceBoundary
canonicalNearFarAllowanceBoundary =
  near-far-allowance-boundary true refl true refl true refl false refl
