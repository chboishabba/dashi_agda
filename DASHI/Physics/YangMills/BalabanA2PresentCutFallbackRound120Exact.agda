{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanA2PresentCutFallbackRound120Exact where

------------------------------------------------------------------------
-- ROUND120 A2 PRESENT-CUT VERDICT
--
-- Inspection of `SharedMarkedAnalyticShellControl` shows that `betaMark` is a
-- nonnegative RESPONSE MAGNITUDE indexed by preceding-history depth.  Its formal
-- interface contains no shooting parameter, no two-history difference and no
-- derivative operator.  Therefore it cannot, by type alone, discharge
-- D_history beta.  Round116 remains a valid shortcut only if a literal
-- same-object derivative theorem is supplied later.
--
-- For the present cut the authoritative route is therefore Round113's explicit
-- source/response kernel:
--
--   r_(n+1) <= R s_n + 1/2 r_n,
--   s_n <= D g_n^4,
--   cubic telescope,
--   -----------------------------
--   q_marg + q_history < 1.
--
-- This file deliberately adds no new estimate; it freezes the BIDI route choice
-- and exposes the already machine-checked full-prefix consumer from the actual
-- Ward response producer.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; _<_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4WardQuarticResponseProducerAdapterExact as Producer
import DASHI.Physics.YangMills.BalabanA2WardResponseBidiClosureRound113Exact as R113
import DASHI.Physics.YangMills.BalabanA2SharedMarkedHistoryDerivativeRound116Exact as R116
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanYM4ShootingSensitivityFromCubicDriftExact as Direct
import DASHI.Physics.YangMills.BalabanYM4RowAAugmentedShootingGateExact as Aug

presentCutTotalSensitivity :
  ∀ {cutoff} → Producer.WardQuarticResponseProducer cutoff → Nat → ℚ
presentCutTotalSensitivity dataSet K =
  let
    augmented = Producer.producerAugmentedShootingData dataSet
    module Paid = Aug.Augmented augmented
  in
  Paid.qTotal K

presentCutTotalSensitivityBelowOne :
  ∀ {cutoff}
    (dataSet : Producer.WardQuarticResponseProducer cutoff)
    K → K Data.Nat.Base.≤ cutoff →
  presentCutTotalSensitivity dataSet K < 1ℚ
presentCutTotalSensitivityBelowOne dataSet K K≤ =
  R113.totalSameHistorySensitivityPrefixBelowOne dataSet K K≤

presentCutFullSensitivityBelowOne :
  ∀ {cutoff}
    (dataSet : Producer.WardQuarticResponseProducer cutoff) →
  presentCutTotalSensitivity dataSet cutoff < 1ℚ
presentCutFullSensitivityBelowOne dataSet =
  R113.totalSameHistorySensitivityFullPrefixBelowOne dataSet

a2PresentCutFallbackCompilerLevel : ProofLevel
a2PresentCutFallbackCompilerLevel = machineChecked

a2PresentCutFullSubunitLevel : ProofLevel
a2PresentCutFullSubunitLevel = machineChecked

-- Optional shortcut remains visible but is NOT used by the authoritative
-- present-cut compiler unless this literal equality is established.
a2OptionalBetaMarkDerivativeIdentificationLevel : ProofLevel
a2OptionalBetaMarkDerivativeIdentificationLevel =
  R116.literalCMP116BetaMarkIsGeneratedHistoryDerivativeLevel

-- Exact surviving physical producer: construct `WardQuarticResponseProducer`
-- from the literal generated CMP109/CMP119 trajectory and identify the actual
-- beta difference with marginal + propagated irrelevant response.  All scalar
-- summation/contraction arithmetic after that source binding is paid above.
literalA2WardResponseProducerLevel : ProofLevel
literalA2WardResponseProducerLevel = Producer.literalWardQuarticResponseProducerLevel

literalA2BetaDifferenceDecompositionLevel : ProofLevel
literalA2BetaDifferenceDecompositionLevel =
  R113.literalCMP109BetaDifferenceIsMarginalPlusIrrelevantLevel
