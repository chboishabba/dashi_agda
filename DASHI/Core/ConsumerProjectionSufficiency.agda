module DASHI.Core.ConsumerProjectionSufficiency where

open import Data.Empty using (⊥)

import DASHI.Core.ConsumerIndexedRelevanceMeasure as Relevance
import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Core.TypedDependencyCore as Dependency

------------------------------------------------------------------------
-- Two independent projection obligations.
--
-- A consumer may have a relevance measure under which the retained region
-- carries all normalized model mass.  That is a static/model-relative claim.
-- Dynamic safety is the stronger trace-congruence obligation from
-- DynamicalQuotientSafety.  Neither is silently substituted for the other.
------------------------------------------------------------------------

record ConsumerMassCertificate
    {Consumer Region Mass : Set}
    (measure : Relevance.ConsumerIndexedRelevanceMeasure Consumer Region Mass)
    (consumer : Consumer) : Set where
  constructor consumerMassCertificate
  field
    accounting : Relevance.OpenWorldMassAccounting measure consumer
    fullRetainedMass : Relevance.FullRetainedModelMass accounting

open ConsumerMassCertificate public

record ConsumerSafeCompression
    {State Action Observation Consumer Region Mass : Set}
    (system : Dependency.DependentActionSystem State Action)
    (project : State → Observation)
    (measure : Relevance.ConsumerIndexedRelevanceMeasure Consumer Region Mass)
    (consumer : Consumer) : Set₁ where
  constructor consumerSafeCompression
  field
    massCertificate : ConsumerMassCertificate measure consumer
    dynamicSafety : Dynamic.DynamicConsumerSafety system project

open ConsumerSafeCompression public

record MassSufficientButDynamicallyUnsafe
    {State Action Observation Consumer Region Mass : Set}
    (system : Dependency.DependentActionSystem State Action)
    (project : State → Observation)
    (measure : Relevance.ConsumerIndexedRelevanceMeasure Consumer Region Mass)
    (consumer : Consumer) : Set₁ where
  constructor massSufficientButDynamicallyUnsafe
  field
    massCertificate : ConsumerMassCertificate measure consumer
    terminalisationDefect : Dynamic.TerminalisationDefect system project

open MassSufficientButDynamicallyUnsafe public

fullMassUnsafeCannotSupplySafeCompression :
  ∀ {State Action Observation Consumer Region Mass}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    {measure : Relevance.ConsumerIndexedRelevanceMeasure Consumer Region Mass}
    {consumer : Consumer} →
  MassSufficientButDynamicallyUnsafe system project measure consumer →
  Dynamic.DynamicConsumerSafety system project →
  ⊥
fullMassUnsafeCannotSupplySafeCompression witness safety =
  Dynamic.terminalisationDefectContradictsSafety
    safety
    (terminalisationDefect witness)
