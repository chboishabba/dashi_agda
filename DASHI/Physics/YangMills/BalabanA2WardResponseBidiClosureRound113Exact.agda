{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanA2WardResponseBidiClosureRound113Exact where

------------------------------------------------------------------------
-- ROUND113 A2: BIDI RESPONSE-KERNEL CLOSURE
--
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Round112 paid the purely marginal/current-coupling response by the mixed
-- Cauchy derivative and cubic telescope.  The older response-kernel lane on
-- master is already stronger than an absolute irrelevant-memory tail: it is a
-- genuine sensitivity recurrence
--
--   r_(n+1) <= R s_n + (1/2) r_n,
--
-- with direct source injection s_n <= D g_n^4.  The quartic source budget and
-- positive-beta cubic telescope give a finite-cutoff S_total, and the response
-- potential converts this to
--
--   sum_{j<K} r_j <= 2 R S_total.
--
-- The Ward/canonical producer then pays the *combined* marginal + irrelevant
-- shooting gate with the same small-coupling choice.  This file exposes that
-- end-to-end theorem directly, rather than leaving Round103's shell q as an
-- apparently independent analytic obligation.
--
-- What remains physical is therefore only the SAME-OBJECT instantiation:
--
--   * identify s_j with the literal preceding-history injection;
--   * prove the literal one-step irrelevant/polymer response inequality;
--   * identify the resulting marginal+irrelevant decomposition with the actual
--     CMP109 beta difference on two generated histories.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as ℕ
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; _+_; _≤_; _<_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4ShootingSensitivityFromCubicDriftExact as Direct
import DASHI.Physics.YangMills.BalabanYM4BetaResponseKernelSummationExact as Kernel
import DASHI.Physics.YangMills.BalabanYM4FiniteBetaResponseKernelBudgetExact as Finite
import DASHI.Physics.YangMills.BalabanYM4QuarticSourceSensitivityBudgetExact as Quartic
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalGateExact as Gate
import DASHI.Physics.YangMills.BalabanYM4RowAAugmentedShootingGateExact as Aug
import DASHI.Physics.YangMills.BalabanYM4WardQuarticResponseProducerAdapterExact as Producer

------------------------------------------------------------------------
-- Forward: literal response kernel partial sum is already bounded by the
-- history constant consumed by the backwards shooting theorem.
------------------------------------------------------------------------

propagatedIrrelevantPrefixBelowHistoryConstant :
  ∀ {cutoff}
    (dataSet : Producer.WardQuarticResponseProducer cutoff)
    K → K ℕ.≤ cutoff →
  Kernel.sum₀
      (Kernel.responseSensitivity (Producer.responseKernel dataSet)) K
  ≤ Gate.quarticResponseHistoryConstant (Producer.quartic dataSet)
propagatedIrrelevantPrefixBelowHistoryConstant dataSet K K≤ =
  Finite.finiteUniformCumulativeResponse
    (Quartic.asFiniteSourceSensitivityBudget (Producer.quartic dataSet))
    K K≤

------------------------------------------------------------------------
-- Backward: the exact producer already lands in the augmented shooting gate.
-- Thus the total marginal + propagated irrelevant coefficient is < 1 for every
-- physical finite prefix.
------------------------------------------------------------------------

totalSameHistorySensitivityPrefixBelowOne :
  ∀ {cutoff}
    (dataSet : Producer.WardQuarticResponseProducer cutoff)
    K → K ℕ.≤ cutoff →
  Direct.sum₀
      (Direct.sensitivity
        (Aug.direct (Producer.producerAugmentedShootingData dataSet))) K
    + Aug.historyConstant (Producer.producerAugmentedShootingData dataSet)
  < 1ℚ
totalSameHistorySensitivityPrefixBelowOne dataSet K K≤ =
  let
    module Paid = Aug.Augmented
      (Producer.producerAugmentedShootingData dataSet)
  in
  Paid.qTotalBelowOne K K≤

totalSameHistorySensitivityFullPrefixBelowOne :
  ∀ {cutoff}
    (dataSet : Producer.WardQuarticResponseProducer cutoff) →
  Direct.sum₀
      (Direct.sensitivity
        (Aug.direct (Producer.producerAugmentedShootingData dataSet))) cutoff
    + Aug.historyConstant (Producer.producerAugmentedShootingData dataSet)
  < 1ℚ
totalSameHistorySensitivityFullPrefixBelowOne {cutoff} dataSet =
  totalSameHistorySensitivityPrefixBelowOne dataSet cutoff ℕ.≤-refl
  where
    import Data.Nat.Properties as ℕ

------------------------------------------------------------------------
-- Authority boundary
------------------------------------------------------------------------

a2ResponseKernelForwardBudgetLevel : ProofLevel
a2ResponseKernelForwardBudgetLevel = machineChecked

a2MarginalPlusIrrelevantSubunitConsumerLevel : ProofLevel
a2MarginalPlusIrrelevantSubunitConsumerLevel = machineChecked

-- No scalar/summability theorem remains after a literal producer is supplied.
-- The remaining A2 leaf is source-coordinate identification of this producer
-- with the actual CMP109/CMP119/CMP122 generated histories and their beta
-- difference.  In particular this is NOT an absolute memory bound and NOT an
-- exponential-forgetting assertion for the marginal coupling.
literalCMP109GeneratedHistoryResponseProducerLevel : ProofLevel
literalCMP109GeneratedHistoryResponseProducerLevel = conditional

literalCMP109BetaDifferenceIsMarginalPlusIrrelevantLevel : ProofLevel
literalCMP109BetaDifferenceIsMarginalPlusIrrelevantLevel = conditional
