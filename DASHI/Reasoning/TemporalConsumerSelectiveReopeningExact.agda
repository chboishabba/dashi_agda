module DASHI.Reasoning.TemporalConsumerSelectiveReopeningExact where

open import DASHI.Core.Prelude

import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Reasoning.TemporalConsumerIndexedSemanticFibreExact as Temporal

------------------------------------------------------------------------
-- CONSUMER-VERSION SELECTIVE REOPENING
--
-- A consumer revision is not a producer/semantic revision.  It has its own
-- dependency source and reopens exactly the certificates whose validity is
-- indexed by the consumer definition/version.
------------------------------------------------------------------------

data TemporalConsumerCertificate : Set where
  consumerDefinitionCertificate
  consumerClosureCertificate
  implicationConeForConsumerCertificate
  downstreamUseCertificate
  semanticProducerCertificate
  : TemporalConsumerCertificate

data ConsumerDepends :
    TemporalConsumerCertificate → TemporalConsumerCertificate → Set where
  definitionFeedsClosure :
    ConsumerDepends consumerDefinitionCertificate consumerClosureCertificate
  closureFeedsCone :
    ConsumerDepends consumerClosureCertificate implicationConeForConsumerCertificate
  coneFeedsUse :
    ConsumerDepends implicationConeForConsumerCertificate downstreamUseCertificate

consumerRevisionReopensClosure :
  Dependency.ReopeningObligation
    ConsumerDepends
    consumerDefinitionCertificate
    consumerClosureCertificate
consumerRevisionReopensClosure =
  Dependency.oneEdgeCreatesReopeningObligation definitionFeedsClosure

consumerRevisionReopensCone :
  Dependency.ReopeningObligation
    ConsumerDepends
    consumerDefinitionCertificate
    implicationConeForConsumerCertificate
consumerRevisionReopensCone =
  Dependency.obligationsCompose
    consumerRevisionReopensClosure
    (Dependency.oneEdgeCreatesReopeningObligation closureFeedsCone)

consumerRevisionReopensDownstreamUse :
  Dependency.ReopeningObligation
    ConsumerDepends
    consumerDefinitionCertificate
    downstreamUseCertificate
consumerRevisionReopensDownstreamUse =
  Dependency.obligationsCompose
    consumerRevisionReopensCone
    (Dependency.oneEdgeCreatesReopeningObligation coneFeedsUse)

------------------------------------------------------------------------
-- A real temporal consumer revision is the authority gate for activating this
-- reopening source.  The dependency path itself cannot manufacture authority.
------------------------------------------------------------------------

record AuthorisedConsumerReopening
    (before after : Temporal.HistoryIndexedSemanticFibre) : Set₁ where
  constructor authorisedConsumerReopening
  field
    revision : Temporal.AuthorisedConsumerRevision before after
    closureReopening :
      Dependency.ReopeningObligation
        ConsumerDepends
        consumerDefinitionCertificate
        consumerClosureCertificate
    coneReopening :
      Dependency.ReopeningObligation
        ConsumerDepends
        consumerDefinitionCertificate
        implicationConeForConsumerCertificate
    downstreamUseReopening :
      Dependency.ReopeningObligation
        ConsumerDepends
        consumerDefinitionCertificate
        downstreamUseCertificate

open AuthorisedConsumerReopening public

authorisedRevisionCreatesSelectiveReopening :
  ∀ {before after} →
  Temporal.AuthorisedConsumerRevision before after →
  AuthorisedConsumerReopening before after
authorisedRevisionCreatesSelectiveReopening revision =
  authorisedConsumerReopening
    revision
    consumerRevisionReopensClosure
    consumerRevisionReopensCone
    consumerRevisionReopensDownstreamUse

------------------------------------------------------------------------
-- Orthogonality / directionality.
------------------------------------------------------------------------

consumerRevisionIsNotSemanticProducerChange :
  ConsumerDepends consumerDefinitionCertificate semanticProducerCertificate → ⊥
consumerRevisionIsNotSemanticProducerChange ()

semanticProducerChangeIsNotConsumerRevision :
  ConsumerDepends semanticProducerCertificate consumerDefinitionCertificate → ⊥
semanticProducerChangeIsNotConsumerRevision ()

record TemporalConsumerSelectiveReopeningBoundary : Set where
  constructor temporalConsumerSelectiveReopeningBoundary
  field
    authorisedConsumerChangeReopensClosure : Bool
    authorisedConsumerChangeReopensClosureIsTrue :
      authorisedConsumerChangeReopensClosure ≡ true
    consumerChangeReopensConeTransitively : Bool
    consumerChangeReopensConeTransitivelyIsTrue :
      consumerChangeReopensConeTransitively ≡ true
    consumerChangeReopensDownstreamUseTransitively : Bool
    consumerChangeReopensDownstreamUseTransitivelyIsTrue :
      consumerChangeReopensDownstreamUseTransitively ≡ true
    consumerChangeIsSemanticProducerChange : Bool
    consumerChangeIsSemanticProducerChangeIsFalse :
      consumerChangeIsSemanticProducerChange ≡ false
    dependencyPathManufacturesRevisionAuthority : Bool
    dependencyPathManufacturesRevisionAuthorityIsFalse :
      dependencyPathManufacturesRevisionAuthority ≡ false

canonicalTemporalConsumerSelectiveReopeningBoundary :
  TemporalConsumerSelectiveReopeningBoundary
canonicalTemporalConsumerSelectiveReopeningBoundary =
  temporalConsumerSelectiveReopeningBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
