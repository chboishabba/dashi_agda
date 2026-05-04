module DASHI.Physics.Closure.EmpiricalCalibrationBridgeToyFitRealDatasetRouteDiagnostic where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.EmpiricalCalibrationBridgeToyFitAuthorityBoundary as C2
import DASHI.Physics.Closure.OriginReceiptPromotionExternalObligation as W8
import DASHI.Physics.Closure.W3AcceptedAuthorityExternalReceiptObligation as W3EXT
import DASHI.Physics.Closure.W3AcceptedAuthorityRouteNarrowing as W3Route

------------------------------------------------------------------------
-- C3 / Noether-Route: real-dataset authority current-route diagnostic.
--
-- C2 already proves that the toy fit cannot supply empirical authority and
-- names the real-dataset route.  This module only records the current state
-- of that route: the positive W3/W8 receipts are still missing, so no W3 or
-- W8 promotion is performed here.

data RealDatasetAuthorityRouteMissing : Set where
  missingW3AcceptedAuthorityExternalReceipt :
    RealDatasetAuthorityRouteMissing
  missingW3AcceptedAuthorityPositiveRoute :
    RealDatasetAuthorityRouteMissing
  missingOriginReceiptPromotionExternalReceipt :
    RealDatasetAuthorityRouteMissing

data RealDatasetAuthorityRouteDiagnosticStatus : Set where
  blockedAwaitingRealDatasetAuthorityReceipts :
    RealDatasetAuthorityRouteDiagnosticStatus

record RealDatasetAuthorityCurrentRouteDiagnostic : Setω where
  field
    c2ToyFitAuthorityBoundary :
      C2.ToyFitAuthorityBoundaryCurrentRoute

    w3AcceptedAuthorityExternalStatus :
      W3EXT.W3AcceptedAuthorityExternalReceiptCurrentStatus

    w3AcceptedAuthorityRouteDiagnostic :
      W3Route.W3AcceptedAuthorityRouteCurrentDiagnostic

    w8OriginReceiptPromotionExternalStatus :
      W8.OriginReceiptPromotionExternalCurrentStatus

    currentStatus :
      RealDatasetAuthorityRouteDiagnosticStatus

    missingRouteReceipts :
      List RealDatasetAuthorityRouteMissing

    exactMissingW3ExternalReceiptName :
      String

    exactMissingW3PositiveRouteName :
      String

    exactMissingW8ExternalReceiptName :
      String

    c2RequiredRouteName :
      String

    routeBoundary :
      List String

    noPromotionBoundary :
      List String

canonicalRealDatasetAuthorityCurrentRouteDiagnostic :
  RealDatasetAuthorityCurrentRouteDiagnostic
canonicalRealDatasetAuthorityCurrentRouteDiagnostic =
  record
    { c2ToyFitAuthorityBoundary =
        C2.canonicalToyFitAuthorityBoundaryCurrentRoute
    ; w3AcceptedAuthorityExternalStatus =
        W3EXT.currentW3AcceptedAuthorityExternalReceiptStatus
    ; w3AcceptedAuthorityRouteDiagnostic =
        W3Route.canonicalW3AcceptedAuthorityRouteCurrentDiagnostic
    ; w8OriginReceiptPromotionExternalStatus =
        W8.canonicalOriginReceiptPromotionExternalCurrentStatus
    ; currentStatus =
        blockedAwaitingRealDatasetAuthorityReceipts
    ; missingRouteReceipts =
        missingW3AcceptedAuthorityExternalReceipt
        ∷ missingW3AcceptedAuthorityPositiveRoute
        ∷ missingOriginReceiptPromotionExternalReceipt
        ∷ []
    ; exactMissingW3ExternalReceiptName =
        "DASHI.Physics.Closure.W3AcceptedAuthorityExternalReceiptObligation.W3AcceptedAuthorityExternalReceipt"
    ; exactMissingW3PositiveRouteName =
        "DASHI.Physics.Closure.W3AcceptedAuthorityRouteNarrowing.W3AcceptedAuthorityPositiveRoute"
    ; exactMissingW8ExternalReceiptName =
        "DASHI.Physics.Closure.OriginReceiptPromotionExternalObligation.OriginReceiptPromotionExternalReceipt"
    ; c2RequiredRouteName =
        "DASHI.Physics.Closure.EmpiricalCalibrationBridgeToyFitAuthorityBoundary.RealDatasetAuthorityReceiptRouteNeeded"
    ; routeBoundary =
        "Current C2 route is still diagnostic-only: the toy fit remains finite-dataset adequacy, not authority"
        ∷ "Real dataset authority still requires W3AcceptedAuthorityExternalReceipt"
        ∷ "Real dataset authority still requires W3AcceptedAuthorityPositiveRoute"
        ∷ "Real dataset authority still requires OriginReceiptPromotionExternalReceipt"
        ∷ []
    ; noPromotionBoundary =
        "This module constructs no W3AcceptedAuthorityExternalReceipt"
        ∷ "This module constructs no W3AcceptedAuthorityPositiveRoute"
        ∷ "This module constructs no OriginReceiptPromotionExternalReceipt"
        ∷ "This module does not promote W3 accepted authority"
        ∷ "This module does not promote W8 origin receipt authority"
        ∷ []
    }

canonicalRealDatasetAuthorityMissingRouteReceipts :
  List RealDatasetAuthorityRouteMissing
canonicalRealDatasetAuthorityMissingRouteReceipts =
  RealDatasetAuthorityCurrentRouteDiagnostic.missingRouteReceipts
    canonicalRealDatasetAuthorityCurrentRouteDiagnostic
