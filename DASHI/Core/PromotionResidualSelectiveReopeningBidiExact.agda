module DASHI.Core.PromotionResidualSelectiveReopeningBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.QueryPromotionResidualBidiExact as QueryPromotion

------------------------------------------------------------------------
-- PROMOTION RESIDUAL -> SELECTIVE REOPENING
--
-- The first failed promotion coordinate becomes the exact reopening target.
-- Earlier closed coordinates remain retained; later coordinates are not allowed
-- to repair an earlier missing obligation.
------------------------------------------------------------------------

data PromotionCoordinate : Set where
  artifactCoordinate
  correspondenceCoordinate
  transportCoordinate
  inhabitanceCoordinate
  : PromotionCoordinate

coordinateForResidual : QueryPromotion.PromotionResidual → PromotionCoordinate
coordinateForResidual QueryPromotion.missingArtifact = artifactCoordinate
coordinateForResidual QueryPromotion.missingCorrespondence = correspondenceCoordinate
coordinateForResidual QueryPromotion.missingTransport = transportCoordinate
coordinateForResidual QueryPromotion.missingTargetInhabitance = inhabitanceCoordinate
coordinateForResidual QueryPromotion.promotionClosed = inhabitanceCoordinate

record PromotionReopeningInstruction (status : QueryPromotion.PromotionStatus) : Set where
  constructor promotion-reopening-instruction
  field
    residual : QueryPromotion.PromotionResidual
    residualMatchesStatus : residual ≡ QueryPromotion.firstPromotionResidual status
    targetCoordinate : PromotionCoordinate
    targetMatchesResidual : targetCoordinate ≡ coordinateForResidual residual
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
    (coordinateForResidual (QueryPromotion.firstPromotionResidual status))
    refl
    (QueryPromotion.producerFor (QueryPromotion.firstPromotionResidual status))
    refl
    "reopen only the first missing promotion coordinate"

threeOfFourReopensOnlyInhabitance :
  targetCoordinate
    (reopeningInstructionFor
      (QueryPromotion.promotion-status true true true false))
  ≡ inhabitanceCoordinate
threeOfFourReopensOnlyInhabitance = refl

missingCorrespondenceReopensCorrespondence :
  targetCoordinate
    (reopeningInstructionFor
      (QueryPromotion.promotion-status true false true true))
  ≡ correspondenceCoordinate
missingCorrespondenceReopensCorrespondence = refl

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
    firstResidualDeterminesReopenCoordinate : Bool
    earlierClosedCoordinatesMayRemainRetained : Bool
    laterStageCanRepairEarlierGap : Bool
    reopeningOneStageRefutesWholePromotionHistory : Bool

canonicalPromotionSelectiveReopeningBoundary : PromotionSelectiveReopeningBoundary
canonicalPromotionSelectiveReopeningBoundary =
  promotion-selective-reopening-boundary true true false false
