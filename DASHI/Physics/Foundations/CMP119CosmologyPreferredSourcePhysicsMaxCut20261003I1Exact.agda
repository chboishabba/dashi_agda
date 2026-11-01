{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261003I1Exact where

------------------------------------------------------------------------
-- PREFERRED SOURCE-NATIVE MAX-CUT / OVERLAY I1 / 2026-10-03.
--
-- The preferred route still has four model-specific payments A1/A2/B1/B2,
-- but B2 is now stated at the correct response order.
--
-- A1  selected rational R144 finite-D1 signed B4 covariance.
-- A2  selected R109 insertion -> one selected cylinder observable semantics.
-- B1  embed(Q_R136) <= embed(DGamma_k) + embed(Tail_109(k)).
-- B2  Tail_109(k) * Z_k < D_Weyl Z_k.
--
-- Fixed-Haar first-variation algebra proves
--
--   D_Weyl Z_k = - N_nonWilson,k,
--
-- so B2 compiler-produces the earlier source numerator margin
--
--   N_nonWilson,k + Tail_109(k) * Z_k < 0.
--
-- The antigravity ordered-Haar theorem concerns a connected derivative of a
-- normalized insertion and therefore cannot directly pay this one-point B2.
-- Also, although the R109 completion estimate is all-cutoff, the present B1
-- interface still requires the finite R144 same-object attachment at the chosen
-- start.  We therefore do not erase B2 merely by invoking dyadic tail decay.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261003HExact as H
import DASHI.Physics.Foundations.CMP119CosmologyPartitionDerivativeTailMarginExact as PartitionB2
import DASHI.Physics.Foundations.CMP119CosmologyConnectedResponseDoesNotPayPartitionB2Exact as Firewall
import DASHI.Physics.Foundations.CMP119CosmologyR109TailMonotonicityExact as TailMonotone

data PreferredSourcePhysicsResidual : Set where
  a1-selected-r144-rational-signed-b4-covariance :
    PreferredSourcePhysicsResidual
  a2-selected-r109-insertion-source-semantics :
    PreferredSourcePhysicsResidual
  b1-direct-r136-r144-r109-tail-anchor :
    PreferredSourcePhysicsResidual
  b2-partition-derivative-beats-r109-tail-debt :
    PreferredSourcePhysicsResidual

preferredSourcePhysicsResidualCount : Nat
preferredSourcePhysicsResidualCount = 4

b2TerminalLeafIsPartitionDerivativeTailDominance : Bool
b2TerminalLeafIsPartitionDerivativeTailDominance =
  PartitionB2.partitionDerivativeTailDominanceIsSufficientForB2

b2IsOnePointResponseNotConnectedNormalizedResponse : Bool
b2IsOnePointResponseNotConnectedNormalizedResponse =
  PartitionB2.sourceFacingB2IsOnePointPartitionResponse

connectedOrderedHaarTracePaysB2Directly : Bool
connectedOrderedHaarTracePaysB2Directly = false

connectedVsPartitionFirewallRecorded : Bool
connectedVsPartitionFirewallRecorded =
  Firewall.orderedHaarConnectedTraceCannotDirectlyPayCosmologyB2

r109TailIsAntitone : Bool
r109TailIsAntitone = TailMonotone.laterScaleNeverIncreasesR109CompletionDebt

tailDecayAloneEliminatesB2AtCurrentB1Interface : Bool
tailDecayAloneEliminatesB2AtCurrentB1Interface = false

b1StillSeparateSameObjectPayment : Bool
b1StillSeparateSameObjectPayment = H.b1IsOneDirectSameObjectTailInequality

remainingAdapterConstructionCount : Nat
remainingAdapterConstructionCount = 0

preferredSourceMaxCutIsStillEvidenceOnly : Bool
preferredSourceMaxCutIsStillEvidenceOnly = true
