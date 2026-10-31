{-# OPTIONS --safe #-}
module DASHI.Biology.SSP15SignedHistoryConsumerBidiExact where

-- Reuse the ACTUAL fifteen-lane FRACTRAN SSPValuation.
-- Sign-only and finite ultrametric charts are projections; the complete
-- valuation is the retained residual until a particular consumer is proved
-- to factor through a strictly smaller representation.

open import DASHI.Core.Prelude
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as SSP
import DASHI.Core.ConsumerIndexedResidualRefinementExact as Residual

SSPHistory : Set
SSPHistory = SSP.SSPValuation

SignedCoarse : Set
SignedCoarse = SSP.SSPPrime → SSP.FibreOrientation

coarse : SSPHistory → SignedCoarse
coarse h p = SSP.orientationOfMultiplicity (h p)

-- Explicit retained signed history, without invented 3^d injectivity.
record FullSSPObserver : Set where
  constructor full-ssp-observer
  field
    orientationChart : SignedCoarse
    signedResidual : SSPHistory
open FullSSPObserver public

encode : SSPHistory → FullSSPObserver
encode h = full-ssp-observer (coarse h) h

decode : FullSSPObserver → SSPHistory
decode observed = signedResidual observed

decodeEncode : (h : SSPHistory) → decode (encode h) ≡ h
decodeEncode h = refl

-- The canonical original histories, not a simulated bit vector.
historyAt : SSPHistory → SSP.SSPPrime → SSP.SignedMultiplicity
historyAt h p = h p

-- Every declared consumer of the actual signed fifteen-lane history
-- factors through the faithful retaining observer, with no scalar assumptions.
consumerFactorsThrough :
  ∀ {Outcome : Set} (consumer : SSPHistory → Outcome) →
  (h : SSPHistory) → consumer (decode (encode h)) ≡ consumer h
consumerFactorsThrough consumer h = refl

retainedObserverSufficient :
  ∀ {Outcome : Set} (consumer : SSPHistory → Outcome) →
  Residual.ConsumerSufficient encode consumer
retainedObserverSufficient consumer x y same =
  cong consumer (cong decode same)

-- Existing necessity theorem: even if two valuations have the same
-- sign-only observer, a consumer-relevant difference forces the complete
-- signed valuation residual to distinguish them.
signCollisionForcesSignedResidual :
  ∀ {Outcome : Set} {consumer : SSPHistory → Outcome} →
  (collision : Residual.ConsumerRelevantCollision coarse consumer) →
  signedResidual (encode (Residual.left collision))
    ≡ signedResidual (encode (Residual.right collision)) → ⊥
signCollisionForcesSignedResidual {consumer = consumer} collision same =
  Residual.differentOutcome collision (cong consumer same)
