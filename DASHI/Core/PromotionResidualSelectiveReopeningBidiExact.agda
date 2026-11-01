module DASHI.Core.PromotionResidualSelectiveReopeningBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.QueryPromotionResidualBidiExact as QueryPromotion

------------------------------------------------------------------------
-- PROMOTION RESIDUAL -> SELECTIVE REOPENING
--
-- The first failed promotion coordinate becomes the exact reopening target.
-- Earlier closed coordinates remain retained; later coordinates are not allowed
-- to repair an earlier missing obligation.  A closed promotion has no reopen
-- target at all.
------------------------------------------------------------------------

data PromotionCoordinate : Set where
  artifactCoordinate : PromotionCoordinate
  correspondenceCoordinate : PromotionCoordinate
  transportCoordinate : PromotionCoordinate
  inhabitanceCoordinate : PromotionCoordinate


data ReopenTarget : Set where
  reopen : PromotionCoordinate → ReopenTarget
  noReopen : ReopenTarget

targetForResidual : QueryPromotion.PromotionResidual → ReopenTarget
targetForResidual QueryPromotion.missingArtifact = reopen artifactCoordinate
targetForResidual QueryPromotion.missingCorrespondence = reopen correspondenceCoordinate
targetForResidual QueryPromotion.missingTransport = reopen transportCoordinate
targetForResidual QueryPromotion.missingTargetInhabitance = reopen inhabitanceCoordinate
targetForResidual QueryPromotion.promotionClosed = noReopen

record PromotionReopeningInstruction (status : QueryPromotion.PromotionStatus) : Set where
  constructor promotion-reopening-instruction
  field
    residual : QueryPromotion.PromotionResidual
    residualMatchesStatus : residual ≡ QueryPromotion.firstPromotionResidual status
    target : ReopenTarget
    targetMatchesResidual : target ≡ targetForResidual residual
    producer : QueryPromotion.ProducerKind
    producerMatchesResidual : producer ≡ QueryPromotion.producerFor residual
    reopeningReference : String

open PromotionReopeningInstruction public

reopeningInstructionFor :
  (status : QueryPromotion.PromotionStatus) →
  PromotionReopeningInstruction status
reopeningInstructionFor status =
  promotion-reopening-instruction
    (QueryPromotion.firstPromotionResidual status)
    refl
    (targetForResidual (QueryPromotion.firstPromotionResidual status))
    refl
    (QueryPromotion.producerFor (QueryPromotion.firstPromotionResidual status))
    refl
    "reopen only the first missing promotion coordinate; closed means no reopen"

threeOfFourReopensOnlyInhabitance :
  target
    (reopeningInstructionFor
      (QueryPromotion.promotion-status true true true false))
  ≡ reopen inhabitanceCoordinate
threeOfFourReopensOnlyInhabitance = refl

missingCorrespondenceReopensCorrespondence :
  target
    (reopeningInstructionFor
      (QueryPromotion.promotion-status true false true true))
  ≡ reopen correspondenceCoordinate
missingCorrespondenceReopensCorrespondence = refl

closedPromotionReopensNothing :
  target
    (reopeningInstructionFor
      (QueryPromotion.promotion-status true true true true))
  ≡ noReopen
closedPromotionReopensNothing = refl

------------------------------------------------------------------------
-- Retention is stage-local.  This is deliberately a logical policy surface,
-- not a claim that a missing target proof leaves every external artifact valid.
------------------------------------------------------------------------

EarlierClosed : PromotionCoordinate → QueryPromotion.PromotionResidual → Set
EarlierClosed artifactCoordinate QueryPromotion.missingArtifact = ⊥
EarlierClosed artifactCoordinate _ = ⊤
EarlierClosed correspondenceCoordinate QueryPromotion.missingArtifact = ⊥
EarlierClosed correspondenceCoordinate QueryPromotion.missingCorrespondence = ⊥
EarlierClosed correspondenceCoordinate _ = ⊤
EarlierClosed transportCoordinate QueryPromotion.missingTransport = ⊥
EarlierClosed transportCoordinate QueryPromotion.missingTargetInhabitance = ⊤
EarlierClosed transportCoordinate QueryPromotion.promotionClosed = ⊤
EarlierClosed transportCoordinate _ = ⊥
EarlierClosed inhabitanceCoordinate QueryPromotion.promotionClosed = ⊤
EarlierClosed inhabitanceCoordinate _ = ⊥

threeOfFourRetainsArtifact :
  EarlierClosed artifactCoordinate QueryPromotion.missingTargetInhabitance
threeOfFourRetainsArtifact = tt

threeOfFourRetainsCorrespondence :
  EarlierClosed correspondenceCoordinate QueryPromotion.missingTargetInhabitance
threeOfFourRetainsCorrespondence = tt

threeOfFourRetainsTransport :
  EarlierClosed transportCoordinate QueryPromotion.missingTargetInhabitance
threeOfFourRetainsTransport = tt

record PromotionSelectiveReopeningBoundary : Set where
  constructor promotion-selective-reopening-boundary
  field
    firstResidualDeterminesReopenTarget : Bool
    closedPromotionHasNoReopenTarget : Bool
    earlierClosedCoordinatesMayRemainRetained : Bool
    laterStageCanRepairEarlierGap : Bool
    reopeningOneStageRefutesWholePromotionHistory : Bool

canonicalPromotionSelectiveReopeningBoundary : PromotionSelectiveReopeningBoundary
canonicalPromotionSelectiveReopeningBoundary =
  promotion-selective-reopening-boundary true true true false false
