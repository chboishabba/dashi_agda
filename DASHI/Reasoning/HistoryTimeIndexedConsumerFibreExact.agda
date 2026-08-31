module DASHI.Reasoning.HistoryTimeIndexedConsumerFibreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.BidiResidualApproximationExact as Bidi

------------------------------------------------------------------------
-- GENERIC HISTORY/TIME-INDEXED CONSUMER FIBRE
--
-- The basic object is not a static hidden-state fibre plus a fixed consumer.
-- It is a section over history and time:
--
--   (h,t) |-> ( F_h(t) , C_h(t) , V_h(t) ).
--
-- Both the live compatible fibre and the downstream consumer may vary over
-- time/history, but they vary through different typed transitions.
------------------------------------------------------------------------

record HistoryTimeConsumerFibreSurface : Set₂ where
  constructor historyTimeConsumerFibreSurface
  field
    History : Set
    Time : Set
    Hidden : Set
    Decision : Set
    ConsumerVersion : Set

    liveFibreAt : History → Time → Bidi.ResidualFibre Hidden
    consumerAt : History → Time → Hidden → Decision
    consumerVersionAt : History → Time → ConsumerVersion

    fibreReading : String
    consumerReading : String
    versionReading : String

open HistoryTimeConsumerFibreSurface public

ConsumerClosedAt :
  (surface : HistoryTimeConsumerFibreSurface) →
  History surface → Time surface → Set
ConsumerClosedAt surface history time =
  Bidi.PointIdentifies
    (liveFibreAt surface history time)
    (consumerAt surface history time)

------------------------------------------------------------------------
-- Producer refinement: change the fibre, freeze the consumer/version.
------------------------------------------------------------------------

record ProducerRefinementAlong
    (surface : HistoryTimeConsumerFibreSurface)
    (history : History surface)
    (before after : Time surface) : Set₁ where
  constructor producerRefinementAlong
  field
    fibreRefines :
      Bidi.FibreRefines
        (liveFibreAt surface history after)
        (liveFibreAt surface history before)
    consumerUnchanged :
      (hidden : Hidden surface) →
      consumerAt surface history after hidden
      ≡ consumerAt surface history before hidden
    consumerVersionUnchanged :
      consumerVersionAt surface history after
      ≡ consumerVersionAt surface history before
    refinementReference : String

open ProducerRefinementAlong public

producerRefinementPreservesConsumerClosure :
  ∀ {surface history before after} →
  ProducerRefinementAlong surface history before after →
  ConsumerClosedAt surface history before →
  ConsumerClosedAt surface history after
producerRefinementPreservesConsumerClosure refinement closed left right leftLive rightLive =
  trans
    (consumerUnchanged refinement left)
    (trans
      (closed left right
        (fibreRefines refinement left leftLive)
        (fibreRefines refinement right rightLive))
      (sym (consumerUnchanged refinement right)))

------------------------------------------------------------------------
-- Consumer revision: freeze the fibre, permit the consumer/version to change
-- only under an application-supplied governance receipt.
------------------------------------------------------------------------

record ConsumerRevisionAuthority
    (surface : HistoryTimeConsumerFibreSurface)
    (history : History surface)
    (before after : Time surface) : Set₁ where
  constructor consumerRevisionAuthority
  field
    sameLiveFibre :
      (hidden : Hidden surface) →
      liveFibreAt surface history after hidden
      ≡ liveFibreAt surface history before hidden
    revisionAuthorityReference : String
    revisionProvenanceReference : String
    requirementPreservationReference : String
    versionTransitionReference : String

open ConsumerRevisionAuthority public

record ConsumerClosureReauditAt
    (surface : HistoryTimeConsumerFibreSurface)
    (history : History surface)
    (before after : Time surface) : Set₁ where
  constructor consumerClosureReauditAt
  field
    authorisedRevision : ConsumerRevisionAuthority surface history before after
    priorClosureReference : String
    newConsumerReference : String
    reauditedClosure : ConsumerClosedAt surface history after
    reauditingReference : String

open ConsumerClosureReauditAt public

------------------------------------------------------------------------
-- Cross-history form. Equality of current fibres does not collapse history:
-- consumers may remain history-indexed even at one shared time coordinate.
------------------------------------------------------------------------

record SameFibreDifferentConsumerAt
    (surface : HistoryTimeConsumerFibreSurface)
    (time : Time surface) : Set₁ where
  constructor sameFibreDifferentConsumerAt
  field
    leftHistory rightHistory : History surface
    sameLiveFibre :
      (hidden : Hidden surface) →
      liveFibreAt surface leftHistory time hidden
      ≡ liveFibreAt surface rightHistory time hidden
    consumerDifferenceWitness : Hidden surface
    consumersDiffer :
      consumerAt surface leftHistory time consumerDifferenceWitness
      ≡ consumerAt surface rightHistory time consumerDifferenceWitness → ⊥

open SameFibreDifferentConsumerAt public

record HistoryTimeConsumerFibreBoundary : Set where
  constructor historyTimeConsumerFibreBoundary
  field
    fibreIsHistoryTimeIndexed : Bool
    fibreIsHistoryTimeIndexedIsTrue : fibreIsHistoryTimeIndexed ≡ true
    consumerIsHistoryTimeIndexed : Bool
    consumerIsHistoryTimeIndexedIsTrue : consumerIsHistoryTimeIndexed ≡ true
    producerRefinementPreservesConsumerVersion : Bool
    producerRefinementPreservesConsumerVersionIsTrue :
      producerRefinementPreservesConsumerVersion ≡ true
    consumerRevisionRequiresSeparateAuthority : Bool
    consumerRevisionRequiresSeparateAuthorityIsTrue :
      consumerRevisionRequiresSeparateAuthority ≡ true
    oldClosureTransportsAcrossArbitraryConsumerRevision : Bool
    oldClosureTransportsAcrossArbitraryConsumerRevisionIsFalse :
      oldClosureTransportsAcrossArbitraryConsumerRevision ≡ false
    sameCurrentFibreImpliesSameHistoryIndexedConsumer : Bool
    sameCurrentFibreImpliesSameHistoryIndexedConsumerIsFalse :
      sameCurrentFibreImpliesSameHistoryIndexedConsumer ≡ false

canonicalHistoryTimeConsumerFibreBoundary : HistoryTimeConsumerFibreBoundary
canonicalHistoryTimeConsumerFibreBoundary =
  historyTimeConsumerFibreBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
