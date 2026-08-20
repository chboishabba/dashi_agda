module DASHI.Core.ConsumerIndexedSemanticDebtExact where

------------------------------------------------------------------------
-- Unresolved/reopenable state is not globally bad.  It becomes mandatory to
-- resolve only for a declared consumer when the distinction matters to that
-- consumer and the consumer's declared margin no longer covers the residual.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true)

record StructuredConsumerDebt
    (Residual Consumer : Set) : Set₁ where
  constructor structuredConsumerDebt
  field
    Matters : Residual → Consumer → Set
    MarginCovers : Residual → Consumer → Set

open StructuredConsumerDebt public

NeedsResolution :
  ∀ {Residual Consumer} →
  StructuredConsumerDebt Residual Consumer →
  Residual → Consumer → Set
NeedsResolution debt residual consumer =
  Matters debt residual consumer
  × ¬ MarginCovers debt residual consumer

record DeferralPolicy
    {Residual Consumer : Set}
    (debt : StructuredConsumerDebt Residual Consumer) : Set₁ where
  constructor deferralPolicy
  field
    Deferred : Residual → Set
    deferredRelevantDebtMustBeCovered :
      ∀ residual consumer →
      Deferred residual →
      Matters debt residual consumer →
      MarginCovers debt residual consumer

open DeferralPolicy public

needsResolutionRefutesDeferral :
  ∀ {Residual Consumer}
    {debt : StructuredConsumerDebt Residual Consumer}
    {policy : DeferralPolicy debt}
    {residual : Residual}
    {consumer : Consumer} →
  NeedsResolution debt residual consumer →
  Deferred policy residual →
  ⊥
needsResolutionRefutesDeferral need deferred =
  proj₂ need
    (deferredRelevantDebtMustBeCovered _ _ deferred (proj₁ need))

ConsumerIrrelevant :
  ∀ {Residual Consumer} →
  StructuredConsumerDebt Residual Consumer →
  Residual → Consumer → Set
ConsumerIrrelevant debt residual consumer =
  Matters debt residual consumer → ⊥

irrelevantResidualCannotNeedResolution :
  ∀ {Residual Consumer}
    {debt : StructuredConsumerDebt Residual Consumer}
    {residual : Residual}
    {consumer : Consumer} →
  ConsumerIrrelevant debt residual consumer →
  NeedsResolution debt residual consumer →
  ⊥
irrelevantResidualCannotNeedResolution irrelevant need =
  irrelevant (proj₁ need)

record ConsumerDebtBoundary : Set where
  constructor consumerDebtBoundary
  field
    unresolvedStateIsNotGloballyErroneous : Bool
    debtIsConsumerIndexed : Bool
    relevantDebtMayBeDeferredWhileMarginCoversIt : Bool
    relevantUncoveredDebtForcesResolution : Bool
    irrelevantResidualNeedNotBeMaterialised : Bool
    debtNeedNotBeOneGlobalScalar : Bool

canonicalConsumerDebtBoundary : ConsumerDebtBoundary
canonicalConsumerDebtBoundary =
  consumerDebtBoundary true true true true true true
