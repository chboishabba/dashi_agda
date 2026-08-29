module DASHI.Programmes.BrainCoarsePersistenceNoGoExact where

open import DASHI.Core.Prelude

import DASHI.Core.FormalClaimTransportGeometryExact as Transport
import DASHI.Programmes.BrainHemibrainExperimentExact as Hemibrain

------------------------------------------------------------------------
-- dashiBRAIN coarse-persistence no-go.
--
-- The checked-in satellite experiments exhibit a concrete forward failure for
-- the neutral/defect geometry candidate under several tested coarse quotients:
-- the fine carrier has nontrivial neutral/defect structure, while the tested
-- random-block and degree-binned quotients collapse to an all-positive fixed
-- point.  Those numerical artifacts remain empirical evidence; Agda does not
-- import their CSV values as axioms.
--
-- What *is* theorem-owned here is the exact backward consequence: if a coarse
-- quotient identifies two fine states that a declared prediction/geometry
-- consumer separates, then that consumer cannot descend through the quotient.
-- Consequently such a quotient cannot discharge `CoarsePersistent` for that
-- consumer merely because its own coarse kernel has defect zero.
------------------------------------------------------------------------

record HemibrainCoarseConsumer
    (Fine Coarse Outcome : Set) : Set₁ where
  constructor hemibrainCoarseConsumer
  field
    coarse : Fine → Coarse
    consumer : Fine → Outcome

open HemibrainCoarseConsumer public

record HemibrainCoarseErasureWitness
    {Fine Coarse Outcome : Set}
    (surface : HemibrainCoarseConsumer Fine Coarse Outcome) : Set where
  constructor hemibrainCoarseErasureWitness
  field
    left right : Fine
    sameCoarse : coarse surface left ≡ coarse surface right
    consumerSeparated : consumer surface left ≡ consumer surface right → ⊥

open HemibrainCoarseErasureWitness public

toClaimNonTransportWitness :
  ∀ {Fine Coarse Outcome : Set}
    {surface : HemibrainCoarseConsumer Fine Coarse Outcome} →
  HemibrainCoarseErasureWitness surface →
  Transport.ClaimNonTransportWitness
    (coarse surface)
    (consumer surface)
toClaimNonTransportWitness witness =
  record
    { left = left witness
    ; right = right witness
    ; sameSurface = sameCoarse witness
    ; differentOutcome = consumerSeparated witness
    }

hemibrainCoarseErasureBlocksConsumerTransport :
  ∀ {Fine Coarse Outcome : Set}
    {surface : HemibrainCoarseConsumer Fine Coarse Outcome} →
  HemibrainCoarseErasureWitness surface →
  Transport.ClaimTransport
    (coarse surface)
    (consumer surface) →
  ⊥
hemibrainCoarseErasureBlocksConsumerTransport witness transport =
  Transport.claimNonTransportWitnessBlocksTransport
    (toClaimNonTransportWitness witness)
    transport

------------------------------------------------------------------------
-- Consumer-indexed persistence package.
--
-- This is deliberately stronger and more useful than a Boolean saying that a
-- coarse graph itself reached a fixed point.  Persistence means that the
-- downstream consumer is reconstructible from the quotient.
------------------------------------------------------------------------

record ConsumerPersistentCoarseGraining
    {Fine Coarse Outcome : Set}
    (surface : HemibrainCoarseConsumer Fine Coarse Outcome) : Set₁ where
  constructor consumerPersistentCoarseGraining
  field
    consumerTransport :
      Transport.ClaimTransport
        (coarse surface)
        (consumer surface)

open ConsumerPersistentCoarseGraining public

erasureWitnessRefutesConsumerPersistence :
  ∀ {Fine Coarse Outcome : Set}
    {surface : HemibrainCoarseConsumer Fine Coarse Outcome} →
  HemibrainCoarseErasureWitness surface →
  ConsumerPersistentCoarseGraining surface →
  ⊥
erasureWitnessRefutesConsumerPersistence witness persistence =
  hemibrainCoarseErasureBlocksConsumerTransport
    witness
    (consumerTransport persistence)

------------------------------------------------------------------------
-- Relation to the generic HemibrainExperimentInterface.
--
-- A future literal instantiation should choose `CoarsePersistent` to contain a
-- consumer-specific transport receipt such as the package above.  A quotient
-- that erases the consumer cannot manufacture the required field from its own
-- zero coarse defect.  Measurement closure remains a separate obligation.
------------------------------------------------------------------------

record BrainCoarsePersistenceBoundary : Set where
  constructor brainCoarsePersistenceBoundary
  field
    zeroCoarseDefectImpliesConsumerPersistence : Bool
    zeroCoarseDefectImpliesConsumerPersistenceIsFalse :
      zeroCoarseDefectImpliesConsumerPersistence ≡ false

    coarseErasureBlocksConsumerTransport : Bool
    coarseErasureBlocksConsumerTransportIsTrue :
      coarseErasureBlocksConsumerTransport ≡ true

    failedRandomBlockPersistenceProvesBiologicalMeaning : Bool
    failedRandomBlockPersistenceProvesBiologicalMeaningIsFalse :
      failedRandomBlockPersistenceProvesBiologicalMeaning ≡ false

    nextUsefulQuotientMustPreserveDeclaredConsumer : Bool
    nextUsefulQuotientMustPreserveDeclaredConsumerIsTrue :
      nextUsefulQuotientMustPreserveDeclaredConsumer ≡ true

canonicalBrainCoarsePersistenceBoundary : BrainCoarsePersistenceBoundary
canonicalBrainCoarsePersistenceBoundary =
  brainCoarsePersistenceBoundary
    false refl
    true refl
    false refl
    true refl
