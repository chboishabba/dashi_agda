module DASHI.Information.PNFHistoryTimeConsumerAuthorityExact where

-- The native balanced-ternary covariance fibre and the canonical
-- history/time-indexed consumer fibre share a *selected* correspondence.
-- Producer-side spectral or covariance refinement does not silently
-- change a downstream consumer version. A consumer revision still
-- needs its separately owned governance/re-audit authority.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Ring
import DASHI.Information.PNFHistoryTimeTernaryCovarianceFibreExact as Native
import DASHI.Reasoning.HistoryTimeIndexedConsumerFibreExact as Historical

record NativeTemporalConsumerLink
  (K : Ring.ExactOrderedCommutativeRing)
  {depth k p : Nat}
  (F : Native.HistoryTimeTernaryCovarianceFibre K depth k p) : Set₂ where
  field
    consumerSurface : Historical.HistoryTimeConsumerFibreSurface
    historyMap :
      Native.History F → Historical.History consumerSurface
    timeMap :
      Native.History F → Native.Time F →
      Historical.Time consumerSurface
    versionCode :
      Historical.ConsumerVersion consumerSurface → Nat
    sameSelectedConsumerVersion :
      (h : Native.History F) → (t : Native.Time F) →
      Native.consumerVersionAt F h t ≡
      versionCode
        (Historical.consumerVersionAt consumerSurface
          (historyMap h) (timeMap h t))

open NativeTemporalConsumerLink public

-- This is the real existing producer-refinement theorem projected onto
-- the SAME point-in-time consumer version in the native covariance fibre.
producerRefinementKeepsNativeConsumerVersion :
  (K : Ring.ExactOrderedCommutativeRing) →
  {depth k p : Nat} →
  (F : Native.HistoryTimeTernaryCovarianceFibre K depth k p) →
  (L : NativeTemporalConsumerLink K F) →
  (h : Native.History F) →
  (before after : Native.Time F) →
  Historical.ProducerRefinementAlong
    (consumerSurface L) (historyMap L h)
    (timeMap L h before) (timeMap L h after) →
  Native.consumerVersionAt F h before ≡
  Native.consumerVersionAt F h after
producerRefinementKeepsNativeConsumerVersion K F L h before after proof =
  trans
    (sameSelectedConsumerVersion L h before)
    (trans
      (cong (versionCode L)
        (sym (Historical.consumerVersionUnchanged proof)))
      (sym (sameSelectedConsumerVersion L h after)))

-- Preserve actual consumer closure under the checked *producer* transition.
-- This theorem does not apply to arbitrary consumer revision.
producerRefinementKeepsDeclaredClosure :
  (K : Ring.ExactOrderedCommutativeRing) →
  {depth k p : Nat} →
  (F : Native.HistoryTimeTernaryCovarianceFibre K depth k p) →
  (L : NativeTemporalConsumerLink K F) →
  (h : Native.History F) →
  (before after : Native.Time F) →
  (proof : Historical.ProducerRefinementAlong
    (consumerSurface L) (historyMap L h)
    (timeMap L h before) (timeMap L h after)) →
  Historical.ConsumerClosedAt
    (consumerSurface L) (historyMap L h) (timeMap L h before) →
  Historical.ConsumerClosedAt
    (consumerSurface L) (historyMap L h) (timeMap L h after)
producerRefinementKeepsDeclaredClosure K F L h before after =
  Historical.producerRefinementPreservesConsumerClosure

-- Reuse the repo's explicit re-audit obligation rather than treating
-- a newly learned spectral state as authorization to revise consumer logic.
authorisedConsumerRevisionNeedsReaudit :
  (K : Ring.ExactOrderedCommutativeRing) →
  {depth k p : Nat} →
  (F : Native.HistoryTimeTernaryCovarianceFibre K depth k p) →
  (L : NativeTemporalConsumerLink K F) →
  (h : Native.History F) →
  (before after : Native.Time F) →
  Historical.ConsumerClosureReauditAt
    (consumerSurface L) (historyMap L h)
    (timeMap L h before) (timeMap L h after) →
  Historical.ConsumerClosedAt
    (consumerSurface L) (historyMap L h) (timeMap L h after)
authorisedConsumerRevisionNeedsReaudit K F L h before after receipt =
  Historical.reauditedClosure receipt
