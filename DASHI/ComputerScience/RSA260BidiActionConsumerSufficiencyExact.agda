module DASHI.ComputerScience.RSA260BidiActionConsumerSufficiencyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Core.ConsumerIndexedResidualLocalizationExact as Local
import DASHI.ComputerScience.RSA260BidiMksolActionSparseObserverExact as Sparse
import DASHI.ComputerScience.RSA260BidiMksolActionChunkedStressExact as Stress

------------------------------------------------------------------------
-- BIDI CONSUMER-SUFFICIENCY BRIDGE
--
-- Direction A: a smaller projection may be adequate for one declared consumer
-- even when it cannot replay the full fine object.
--
-- Direction B: a consumer-separated collision reopens exactly the residual
-- information needed to repair that projection.
--
-- The generic Core owner already proves witness-level residual localisation;
-- this file only records the RSA action-consumer instantiation and the current
-- finite payment boundary.  It introduces no new planner or adequacy calculus.
------------------------------------------------------------------------

localizationBoundary : Local.ConsumerIndexedResidualLocalizationBoundary
localizationBoundary = Local.canonicalConsumerIndexedResidualLocalizationBoundary

sparseBoundary : Sparse.MksolActionSparseObserverBoundary
sparseBoundary = Sparse.canonicalMksolActionSparseObserverBoundary

stressBoundary : Stress.MksolActionChunkedStressBoundary
stressBoundary = Stress.canonicalMksolActionChunkedStressBoundary

------------------------------------------------------------------------
-- WrongType / cross-consumer firewalls.
------------------------------------------------------------------------

data ReceiptIdentityMinimalityTransfersToAction : Set where
data TwelveWorldAdequacyCreatesThirtyFourWorldAdequacy : Set where
data SyntheticAdequacyCreatesProductionCADOAdequacy : Set where
data CollisionRequiresReturningToFullReplay : Set where

receiptIdentityMinimalityDoesNotTransferToAction :
  ReceiptIdentityMinimalityTransfersToAction -> ⊥
receiptIdentityMinimalityDoesNotTransferToAction ()

twelveWorldAdequacyDoesNotCreateThirtyFourWorldAdequacy :
  TwelveWorldAdequacyCreatesThirtyFourWorldAdequacy -> ⊥
twelveWorldAdequacyDoesNotCreateThirtyFourWorldAdequacy ()

syntheticAdequacyDoesNotCreateProductionCADOAdequacy :
  SyntheticAdequacyCreatesProductionCADOAdequacy -> ⊥
syntheticAdequacyDoesNotCreateProductionCADOAdequacy ()

collisionDoesNotForceFullReplay : CollisionRequiresReturningToFullReplay -> ⊥
collisionDoesNotForceFullReplay ()

record RSAActionConsumerSufficiencyBoundary : Set where
  constructor rsa-action-consumer-sufficiency-boundary
  field
    consumerIndexedSufficiencyIsPrimary : Bool
    collisionReopensResidualCoordinate : Bool
    exactReplayRemainsSufficientUpperEndpoint : Bool
    receiptIdentityMinimalityTransfersToAction : Bool
    currentTwelveWorldDegreeR2R10AdequacyPaid : Bool
    broaderThirtyFourWorldAdequacyPaid : Bool
    productionCADOSameObjectAdequacyPaid : Bool
    nextResidual : String
open RSAActionConsumerSufficiencyBoundary public

canonicalRSAActionConsumerSufficiencyBoundary : RSAActionConsumerSufficiencyBoundary
canonicalRSAActionConsumerSufficiencyBoundary =
  rsa-action-consumer-sufficiency-boundary
    true
    true
    true
    false
    true
    false
    false
    "stress the smallest currently adequate action observer rather than the harder receipt-identity observer. If a complete broader action portfolio produces a collision, retain that collision as a LocalizedResidualWitness and add only a coordinate that separates the action consumer inside the failed fibre. Exact coefficient replay remains the sufficient upper endpoint, not the default target."
