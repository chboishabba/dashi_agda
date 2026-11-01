module DASHI.Cognition.PNF.RelationalPerspectiveFactorsThroughExact where

------------------------------------------------------------------------
-- RELATIONAL PERSPECTIVE QUOTIENT SAFETY
--
-- Reuse the canonical consumer-descent theorem rather than introducing a new
-- factorisation notion.  A coarse observer is admissible for a declared
-- consumer exactly when the consumer is constant on its fibres; on a sectioned
-- projection this is equivalent to an explicit factorisation witness.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.SectionedProjectionProvenanceBridgeExact as Sectioned

RelationalConsumerAdequate :
  ∀ {State Surface Outcome : Set} →
  (State → Surface) →
  (State → Outcome) →
  Set
RelationalConsumerAdequate observe consumer =
  Descent.ConsumerSufficient observe consumer

relationalConsumerAdequacyIffFibreConstancy :
  ∀ {State Surface Outcome : Set}
    (observe : State → Surface)
    (consumer : State → Outcome) →
  Descent.ConsumerSufficient observe consumer →
  Descent.FibreConstantFor observe consumer
relationalConsumerAdequacyIffFibreConstancy observe consumer =
  Descent.consumerSufficientIsFibreConstant

sectionedRelationalAdequacyIffFactorisation :
  ∀ {State Surface Outcome : Set}
    (projection : Sectioned.SectionedProjection State Surface)
    (consumer : State → Outcome) →
  Descent.LogicalIff₁₀
    (Descent.FactorsThrough (Sectioned.project projection) consumer)
    (Descent.ConsumerSufficient (Sectioned.project projection) consumer)
sectionedRelationalAdequacyIffFactorisation =
  Descent.sectionedDescentIffConsumerSufficient

record RelationalPerspectiveFactorBoundary : Set where
  constructor relational-perspective-factor-boundary
  field
    oneCoarseObserverIsAdequateForEveryConsumer : Bool
    adequacyIsConsumerIndexed : Bool
    fibreConstancyIsRequired : Bool
    sectionedAdequacyCanConstructExplicitFactorisation : Bool
    consumerAdequacyMeansWorldCompleteness : Bool

canonicalRelationalPerspectiveFactorBoundary :
  RelationalPerspectiveFactorBoundary
canonicalRelationalPerspectiveFactorBoundary =
  relational-perspective-factor-boundary false true true true false
