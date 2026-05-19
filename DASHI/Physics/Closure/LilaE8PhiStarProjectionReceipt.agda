module DASHI.Physics.Closure.LilaE8PhiStarProjectionReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataT43SudakovBaselinePredictionHook as HEPBaseline
import DASHI.Physics.Closure.LamTungE8AdapterSurface as LamTung
import DASHI.Physics.Closure.LilaE8RootEnumeration as RootEnum
import DASHI.Physics.Closure.LilaE8ThetaJBridgeSurface as ThetaJ

------------------------------------------------------------------------
-- LILA-R5: parked phi-star projection receipt request.
--
-- This surface is the dependent integration point:
--
--   LILA-R2 root-enumeration receipt
--   LILA-R3 Lam-Tung/E8 adapter receipt
--   LILA-R4 E8 theta/J bridge receipt
--       -> LILA-R5 phi-star projection receipt
--       -> HEP-R33 accepted DASHI phi-star prediction API
--
-- The current upstream lanes are request/diagnostic surfaces only, so R5 is
-- explicitly parked and non-promoting.

data LilaE8PhiStarProjectionReceiptStatus : Set where
  parkedAwaitingR2R3R4Receipts :
    LilaE8PhiStarProjectionReceiptStatus

data LilaE8PhiStarProjectionInput : Set where
  e8RootEnumerationConstructiveReceipt :
    LilaE8PhiStarProjectionInput
  lamTungE8AdapterReceipt :
    LilaE8PhiStarProjectionInput
  e8ThetaJBridgeReceipt :
    LilaE8PhiStarProjectionInput
  phiStarDiagonalProjectionLaw :
    LilaE8PhiStarProjectionInput
  t43BinIntegralSemantics :
    LilaE8PhiStarProjectionInput
  digestBoundProjectionRunner :
    LilaE8PhiStarProjectionInput
  cleanPredictionFreeze :
    LilaE8PhiStarProjectionInput
  comparisonLawReceipt :
    LilaE8PhiStarProjectionInput

canonicalLilaE8PhiStarProjectionInputs :
  List LilaE8PhiStarProjectionInput
canonicalLilaE8PhiStarProjectionInputs =
  e8RootEnumerationConstructiveReceipt
  ∷ lamTungE8AdapterReceipt
  ∷ e8ThetaJBridgeReceipt
  ∷ phiStarDiagonalProjectionLaw
  ∷ t43BinIntegralSemantics
  ∷ digestBoundProjectionRunner
  ∷ cleanPredictionFreeze
  ∷ comparisonLawReceipt
  ∷ []

data LilaE8PhiStarProjectionBlocker : Set where
  rootEnumerationIsRequestOnly :
    LilaE8PhiStarProjectionBlocker
  lamTungAdapterIsRequestOnly :
    LilaE8PhiStarProjectionBlocker
  thetaJBridgeIsRequestOnly :
    LilaE8PhiStarProjectionBlocker
  missingDiagonalProjectionLaw :
    LilaE8PhiStarProjectionBlocker
  missingT43ProjectionArtifact :
    LilaE8PhiStarProjectionBlocker
  missingAcceptedDASHIPredictionAPI :
    LilaE8PhiStarProjectionBlocker
  sudakovBaselineIsNotDASHIProjection :
    LilaE8PhiStarProjectionBlocker
  missingComparisonLawReceipt :
    LilaE8PhiStarProjectionBlocker

canonicalLilaE8PhiStarProjectionBlockers :
  List LilaE8PhiStarProjectionBlocker
canonicalLilaE8PhiStarProjectionBlockers =
  rootEnumerationIsRequestOnly
  ∷ lamTungAdapterIsRequestOnly
  ∷ thetaJBridgeIsRequestOnly
  ∷ missingDiagonalProjectionLaw
  ∷ missingT43ProjectionArtifact
  ∷ missingAcceptedDASHIPredictionAPI
  ∷ sudakovBaselineIsNotDASHIProjection
  ∷ missingComparisonLawReceipt
  ∷ []

data LilaE8PhiStarProjectionBoundary : Set where
  noProjectionReceiptHere :
    LilaE8PhiStarProjectionBoundary
  noAcceptedPredictionAPIHere :
    LilaE8PhiStarProjectionBoundary
  noCleanFreezeHere :
    LilaE8PhiStarProjectionBoundary
  noComparisonLawHere :
    LilaE8PhiStarProjectionBoundary
  noW3W4W5W8PromotionHere :
    LilaE8PhiStarProjectionBoundary

canonicalLilaE8PhiStarProjectionBoundaries :
  List LilaE8PhiStarProjectionBoundary
canonicalLilaE8PhiStarProjectionBoundaries =
  noProjectionReceiptHere
  ∷ noAcceptedPredictionAPIHere
  ∷ noCleanFreezeHere
  ∷ noComparisonLawHere
  ∷ noW3W4W5W8PromotionHere
  ∷ []

data LilaE8PhiStarProjectionAcceptedReceipt : Set where

lilaE8PhiStarProjectionAcceptedReceiptImpossibleHere :
  LilaE8PhiStarProjectionAcceptedReceipt →
  ⊥
lilaE8PhiStarProjectionAcceptedReceiptImpossibleHere ()

record LilaE8PhiStarProjectionReceiptRequest : Setω where
  field
    status :
      LilaE8PhiStarProjectionReceiptStatus

    rootEnumerationRequest :
      RootEnum.LilaE8RootEnumerationRequest

    rootEnumerationStillRequestOnly :
      RootEnum.LilaE8RootEnumerationRequest.theoremCompletedHere
        rootEnumerationRequest
      ≡
      false

    lamTungAdapterSurface :
      LamTung.LamTungE8AdapterSurface

    lamTungAdapterStillRequestOnly :
      LamTung.LamTungE8AdapterSurface.adapterConstructedHere
        lamTungAdapterSurface
      ≡
      false

    thetaJBridgeSurface :
      ThetaJ.LilaE8ThetaJBridgeSurface

    thetaJBridgeStillRequestOnly :
      ThetaJ.LilaE8ThetaJBridgeSurface.bridgeCompletedHere
        thetaJBridgeSurface
      ≡
      false

    sudakovBaselineHook :
      HEPBaseline.HEPDataT43SudakovBaselinePredictionHook

    sudakovBaselineAcceptedAsDASHIAPI :
      Bool

    sudakovBaselineAcceptedAsDASHIAPIIsFalse :
      sudakovBaselineAcceptedAsDASHIAPI ≡ false

    projectionReceiptConstructedHere :
      Bool

    projectionReceiptConstructedHereIsFalse :
      projectionReceiptConstructedHere ≡ false

    acceptedDASHIPredictionAPIConstructedHere :
      Bool

    acceptedDASHIPredictionAPIConstructedHereIsFalse :
      acceptedDASHIPredictionAPIConstructedHere ≡ false

    requiredInputs :
      List LilaE8PhiStarProjectionInput

    requiredInputsAreCanonical :
      requiredInputs ≡ canonicalLilaE8PhiStarProjectionInputs

    blockers :
      List LilaE8PhiStarProjectionBlocker

    blockersAreCanonical :
      blockers ≡ canonicalLilaE8PhiStarProjectionBlockers

    requestedRouteShape :
      String

    requestedRouteShapeIsCanonical :
      requestedRouteShape
      ≡
      "R2 E8 roots + R3 Lam-Tung/E8 adapter + R4 theta/J bridge -> phi-star diagonal projection -> t43 prediction API"

    nonPromotionBoundary :
      List LilaE8PhiStarProjectionBoundary

    nonPromotionBoundaryIsCanonical :
      nonPromotionBoundary ≡ canonicalLilaE8PhiStarProjectionBoundaries

    acceptedReceiptBlocked :
      LilaE8PhiStarProjectionAcceptedReceipt →
      ⊥

canonicalLilaE8PhiStarProjectionReceiptRequest :
  LilaE8PhiStarProjectionReceiptRequest
canonicalLilaE8PhiStarProjectionReceiptRequest =
  record
    { status =
        parkedAwaitingR2R3R4Receipts
    ; rootEnumerationRequest =
        RootEnum.canonicalLilaE8RootEnumerationRequest
    ; rootEnumerationStillRequestOnly =
        refl
    ; lamTungAdapterSurface =
        LamTung.canonicalLamTungE8AdapterSurface
    ; lamTungAdapterStillRequestOnly =
        refl
    ; thetaJBridgeSurface =
        ThetaJ.canonicalLilaE8ThetaJBridgeSurface
    ; thetaJBridgeStillRequestOnly =
        refl
    ; sudakovBaselineHook =
        HEPBaseline.canonicalHEPDataT43SudakovBaselinePredictionHook
    ; sudakovBaselineAcceptedAsDASHIAPI =
        false
    ; sudakovBaselineAcceptedAsDASHIAPIIsFalse =
        refl
    ; projectionReceiptConstructedHere =
        false
    ; projectionReceiptConstructedHereIsFalse =
        refl
    ; acceptedDASHIPredictionAPIConstructedHere =
        false
    ; acceptedDASHIPredictionAPIConstructedHereIsFalse =
        refl
    ; requiredInputs =
        canonicalLilaE8PhiStarProjectionInputs
    ; requiredInputsAreCanonical =
        refl
    ; blockers =
        canonicalLilaE8PhiStarProjectionBlockers
    ; blockersAreCanonical =
        refl
    ; requestedRouteShape =
        "R2 E8 roots + R3 Lam-Tung/E8 adapter + R4 theta/J bridge -> phi-star diagonal projection -> t43 prediction API"
    ; requestedRouteShapeIsCanonical =
        refl
    ; nonPromotionBoundary =
        canonicalLilaE8PhiStarProjectionBoundaries
    ; nonPromotionBoundaryIsCanonical =
        refl
    ; acceptedReceiptBlocked =
        lilaE8PhiStarProjectionAcceptedReceiptImpossibleHere
    }

canonicalLilaE8PhiStarProjectionStatus :
  LilaE8PhiStarProjectionReceiptStatus
canonicalLilaE8PhiStarProjectionStatus =
  LilaE8PhiStarProjectionReceiptRequest.status
    canonicalLilaE8PhiStarProjectionReceiptRequest
