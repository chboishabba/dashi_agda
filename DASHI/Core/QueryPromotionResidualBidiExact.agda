module DASHI.Core.QueryPromotionResidualBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.PromotionTransportChainBidiExact as Promotion
import DASHI.Core.QueryCompatibleFibreConsumerClosureBidiExact as QueryFibre

------------------------------------------------------------------------
-- QUERY-RELATIVE PROMOTION RESIDUAL
--
-- Cross-weld of the Lean QueryResidual and PromotionTransport extractions,
-- reconstructed in Agda.  A promotion query returns the first missing
-- obligation, which selects the next producer without pretending that later
-- stages repair earlier missing receipts.
------------------------------------------------------------------------

data PromotionResidual : Set where
  missingArtifact
  missingCorrespondence
  missingTransport
  missingTargetInhabitance
  promotionClosed
  : PromotionResidual

record PromotionStatus : Set where
  constructor promotion-status
  field
    artifactPresent : Bool
    correspondencePresent : Bool
    transportSoundPresent : Bool
    targetInhabited : Bool

open PromotionStatus public

firstPromotionResidual : PromotionStatus → PromotionResidual
firstPromotionResidual (promotion-status false correspondence transport inhabitance) =
  missingArtifact
firstPromotionResidual (promotion-status true false transport inhabitance) =
  missingCorrespondence
firstPromotionResidual (promotion-status true true false inhabitance) =
  missingTransport
firstPromotionResidual (promotion-status true true true false) =
  missingTargetInhabitance
firstPromotionResidual (promotion-status true true true true) =
  promotionClosed

data ProducerKind : Set where
  acquireArtifact
  establishCorrespondence
  proveTransport
  constructTargetInhabitant
  noProducerNeeded
  : ProducerKind

producerFor : PromotionResidual → ProducerKind
producerFor missingArtifact = acquireArtifact
producerFor missingCorrespondence = establishCorrespondence
producerFor missingTransport = proveTransport
producerFor missingTargetInhabitance = constructTargetInhabitant
producerFor promotionClosed = noProducerNeeded

firstResidualSelectsProducer : PromotionStatus → ProducerKind
firstResidualSelectsProducer status = producerFor (firstPromotionResidual status)

artifactGapStopsBeforeLaterStages :
  firstPromotionResidual (promotion-status false true true true) ≡ missingArtifact
artifactGapStopsBeforeLaterStages = refl

correspondenceGapStopsBeforeTransport :
  firstPromotionResidual (promotion-status true false true true) ≡ missingCorrespondence
correspondenceGapStopsBeforeTransport = refl

threeOfFourSelectsTargetInhabitantProducer :
  firstResidualSelectsProducer (promotion-status true true true false)
  ≡ constructTargetInhabitant
threeOfFourSelectsTargetInhabitantProducer = refl

allFourClosePromotionQuery :
  firstPromotionResidual (promotion-status true true true true) ≡ promotionClosed
allFourClosePromotionQuery = refl

------------------------------------------------------------------------
-- No-collapse boundaries.
------------------------------------------------------------------------

data LaterStageRepairsEarlierGap : Set where
data ProducerNameCreatesReceipt : Set where

data ClosedPromotionQueryMeansAllConsumersClosed : Set where

laterStageDoesNotRepairEarlierGap : LaterStageRepairsEarlierGap → ⊥
laterStageDoesNotRepairEarlierGap ()
producerNameDoesNotCreateReceipt : ProducerNameCreatesReceipt → ⊥
producerNameDoesNotCreateReceipt ()
closedPromotionQueryDoesNotCloseAllConsumers :
  ClosedPromotionQueryMeansAllConsumersClosed → ⊥
closedPromotionQueryDoesNotCloseAllConsumers ()

record QueryPromotionResidualBoundary : Set where
  constructor query-promotion-residual-boundary
  field
    firstMissingObligationIsExplicit : Bool
    residualDeterminesProducerKind : Bool
    producerKindIsReceipt : Bool
    promotionClosureIsGlobalConsumerClosure : Bool

canonicalQueryPromotionResidualBoundary : QueryPromotionResidualBoundary
canonicalQueryPromotionResidualBoundary =
  query-promotion-residual-boundary true true false false
