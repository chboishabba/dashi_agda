module DASHI.Programmes.CFDChartCorrectionExact where

open import DASHI.Core.Prelude

import DASHI.Core.FormalClaimTransportGeometryExact as Transport
import DASHI.Programmes.BidirectionalSatelliteCorrectionExact as BIDI

------------------------------------------------------------------------
-- BIDI cut for dashiCFD / LES-style reduced charts.
--
-- The mathematically correct statement is consumer-relative.  A reduced chart
-- is unusable for a fine claim exactly when it identifies two physical states
-- that the claim separates.  No deterministic closure or relabelling can
-- restore that lost distinction.  A corrected CFD representation must enlarge
-- the carried state enough to remove the non-descent witness for the consumer
-- actually being claimed.
------------------------------------------------------------------------

CFDClaimLossWitness :
  ∀ {State Reduced Claim : Set} →
  (State → Reduced) →
  (State → Claim) → Set
CFDClaimLossWitness reduced claim =
  Transport.ClaimNonTransportWitness reduced claim

reducedChartCollisionBlocksFineClaim :
  ∀ {State Reduced Claim : Set}
    {reduced : State → Reduced}
    {claim : State → Claim} →
  CFDClaimLossWitness reduced claim →
  Transport.ClaimTransport reduced claim →
  ⊥
reducedChartCollisionBlocksFineClaim =
  Transport.claimNonTransportWitnessBlocksTransport

collisionForcesRepresentationRepair :
  ∀ {State Reduced Formal Claim : Set}
    {reduced : State → Reduced}
    {formal : State → Formal}
    {claim : State → Claim} →
  CFDClaimLossWitness reduced claim →
  BIDI.CorrectedSatelliteBridge reduced formal claim →
  ⊥
collisionForcesRepresentationRepair =
  BIDI.informationLossBlocksCorrectedBridge

------------------------------------------------------------------------
-- Once an augmented state carries enough information to commute with the
-- already-owned formal chart, the existing formal theorem transports without
-- re-proving the downstream mathematics inside dashiCFD.
------------------------------------------------------------------------

augmentedCFDStateReusesFormalClaim :
  ∀ {State Augmented Formal Claim : Set}
    {augmented : State → Augmented}
    {formal : State → Formal}
    {claim : State → Claim} →
  BIDI.CorrectedSatelliteBridge augmented formal claim →
  Transport.ClaimTransport augmented claim
augmentedCFDStateReusesFormalClaim =
  BIDI.correctedSatelliteYieldsClaimTransport

record CFDChartCorrectionBoundary : Set where
  constructor cfdChartCorrectionBoundary
  field
    closureModelCanRecoverDiscardedClaimInformation : Bool
    closureModelCanRecoverDiscardedClaimInformationIsFalse :
      closureModelCanRecoverDiscardedClaimInformation ≡ false

    moreAtomsMayRepairAConsumerSpecificCollision : Bool
    moreAtomsMayRepairAConsumerSpecificCollisionIsTrue :
      moreAtomsMayRepairAConsumerSpecificCollision ≡ true

    empiricalFrameConditionIsContinuumNormEquivalence : Bool
    empiricalFrameConditionIsContinuumNormEquivalenceIsFalse :
      empiricalFrameConditionIsContinuumNormEquivalence ≡ false

canonicalCFDChartCorrectionBoundary : CFDChartCorrectionBoundary
canonicalCFDChartCorrectionBoundary =
  cfdChartCorrectionBoundary
    false refl
    true refl
    false refl
