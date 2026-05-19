module DASHI.Physics.Closure.EmpiricalCalibrationBridgeToyFitAuthorityBoundary where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.Closure.EmpiricalCalibrationBridgeToyFit as Toy
import DASHI.Physics.Closure.OriginReceiptPromotionExternalObligation as W8
import DASHI.Physics.Closure.W3AcceptedAuthorityExternalReceiptObligation as W3EXT
import DASHI.Physics.Closure.W3AcceptedAuthorityRouteNarrowing as W3Route

------------------------------------------------------------------------
-- Option C toy-fit authority boundary.
--
-- The finite toy fit proves only local residual acceptance.  The authority
-- token exported by the toy-fit module is constructorless, so toy adequacy
-- cannot become external empirical authority or promote the W3/W8 lanes.

data ToyFitAuthorityBoundaryFinding : Set where
  finiteToyFitAdequacyOnly :
    ToyFitAuthorityBoundaryFinding
  toyFitAuthorityTokenConstructorless :
    ToyFitAuthorityBoundaryFinding
  realDatasetAuthorityReceiptNeeded :
    ToyFitAuthorityBoundaryFinding
  w3AcceptedAuthorityRouteStillExternal :
    ToyFitAuthorityBoundaryFinding
  w8OriginPromotionRouteStillExternal :
    ToyFitAuthorityBoundaryFinding
  noW3W8PromotionFromToyFit :
    ToyFitAuthorityBoundaryFinding

data ToyFitAuthorityBoundaryImpossible : Set where

toyFitAuthorityTokenImpossibleHere :
  ExternalEmpiricalAuthorityToken →
  ToyFitAuthorityBoundaryImpossible
toyFitAuthorityTokenImpossibleHere ()

toyFitAdequacyCannotSupplyExternalAuthority :
  (fit : EmpiricalCalibrationBridgeToyFit) →
  ExternalEmpiricalAuthorityToken →
  ToyFitNotExternalAuthority
toyFitAdequacyCannotSupplyExternalAuthority fit =
  EmpiricalCalibrationBridgeToyFit.toyFitDoesNotProvideExternalAuthority fit

canonicalToyFitAdequacyCannotSupplyExternalAuthority :
  ExternalEmpiricalAuthorityToken →
  ToyFitNotExternalAuthority
canonicalToyFitAdequacyCannotSupplyExternalAuthority =
  toyFitAdequacyCannotSupplyExternalAuthority
    canonicalEmpiricalCalibrationBridgeToyFit

canonicalToyFitAuthorityBoundaryScope :
  ToyFitBoundaryReceipt.scope
    (EmpiricalCalibrationBridgeToyFit.adequacyBoundary
      canonicalEmpiricalCalibrationBridgeToyFit)
  ≡
  finiteDatasetToyFitOnly
canonicalToyFitAuthorityBoundaryScope =
  refl

------------------------------------------------------------------------
-- Positive route shape, named but not constructed.

record RealDatasetAuthorityReceiptRouteNeeded : Setω where
  field
    w3AcceptedAuthorityExternalReceipt :
      W3EXT.W3AcceptedAuthorityExternalReceipt

    w3AcceptedAuthorityPositiveRoute :
      W3Route.W3AcceptedAuthorityPositiveRoute

    w8OriginReceiptPromotionExternalReceipt :
      W8.OriginReceiptPromotionExternalReceipt

record ToyFitAuthorityBoundaryCurrentRoute : Setω where
  field
    toyFit :
      EmpiricalCalibrationBridgeToyFit

    toyFitBoundaryReceipt :
      ToyFitBoundaryReceipt

    toyFitScopeIsFiniteOnly :
      ToyFitBoundaryReceipt.scope toyFitBoundaryReceipt
      ≡
      finiteDatasetToyFitOnly

    toyFitExternalAuthorityEliminates :
      ExternalEmpiricalAuthorityToken →
      ToyFitNotExternalAuthority

    toyFitExternalAuthorityImpossible :
      ExternalEmpiricalAuthorityToken →
      ToyFitAuthorityBoundaryImpossible

    w3AcceptedAuthorityCurrentDiagnostic :
      W3Route.W3AcceptedAuthorityRouteCurrentDiagnostic

    w8OriginPromotionCurrentStatus :
      W8.OriginReceiptPromotionExternalCurrentStatus

    findings :
      List ToyFitAuthorityBoundaryFinding

    exactRealDatasetReceiptNeeded :
      String

    exactW3RouteName :
      String

    exactW8RouteName :
      String

    sourceBoundary :
      List String

    noPromotionBoundary :
      List String

canonicalToyFitAuthorityBoundaryCurrentRoute :
  ToyFitAuthorityBoundaryCurrentRoute
canonicalToyFitAuthorityBoundaryCurrentRoute =
  record
    { toyFit =
        canonicalEmpiricalCalibrationBridgeToyFit
    ; toyFitBoundaryReceipt =
        EmpiricalCalibrationBridgeToyFit.adequacyBoundary
          canonicalEmpiricalCalibrationBridgeToyFit
    ; toyFitScopeIsFiniteOnly =
        refl
    ; toyFitExternalAuthorityEliminates =
        canonicalToyFitAdequacyCannotSupplyExternalAuthority
    ; toyFitExternalAuthorityImpossible =
        toyFitAuthorityTokenImpossibleHere
    ; w3AcceptedAuthorityCurrentDiagnostic =
        W3Route.canonicalW3AcceptedAuthorityRouteCurrentDiagnostic
    ; w8OriginPromotionCurrentStatus =
        W8.canonicalOriginReceiptPromotionExternalCurrentStatus
    ; findings =
        finiteToyFitAdequacyOnly
        ∷ toyFitAuthorityTokenConstructorless
        ∷ realDatasetAuthorityReceiptNeeded
        ∷ w3AcceptedAuthorityRouteStillExternal
        ∷ w8OriginPromotionRouteStillExternal
        ∷ noW3W8PromotionFromToyFit
        ∷ []
    ; exactRealDatasetReceiptNeeded =
        "RealDatasetAuthorityReceiptRouteNeeded: supply W3AcceptedAuthorityExternalReceipt, W3AcceptedAuthorityPositiveRoute, and OriginReceiptPromotionExternalReceipt from real dataset authority"
    ; exactW3RouteName =
        "DASHI.Physics.Closure.W3AcceptedAuthorityRouteNarrowing.W3AcceptedAuthorityPositiveRoute"
    ; exactW8RouteName =
        "DASHI.Physics.Closure.OriginReceiptPromotionExternalObligation.OriginReceiptPromotionExternalReceipt"
    ; sourceBoundary =
        "Option C finite toy observations discharge only EmpiricalCalibrationBridgeToyFit.datasetAccepted"
        ∷ "The toy-fit ExternalEmpiricalAuthorityToken has no constructor"
        ∷ "Real dataset authority must arrive through W3AcceptedAuthorityExternalReceipt and OriginReceiptPromotionExternalReceipt, not through toy residual acceptance"
        ∷ []
    ; noPromotionBoundary =
        "This module does not construct ExternalEmpiricalAuthorityToken"
        ∷ "This module does not construct W3AcceptedAuthorityExternalReceipt"
        ∷ "This module does not construct W3AcceptedAuthorityPositiveRoute"
        ∷ "This module does not construct OriginReceiptPromotionExternalReceipt"
        ∷ "No W3/W8 empirical promotion is inhabited here"
        ∷ []
    }

canonicalToyFitAuthorityBoundaryFindings :
  List ToyFitAuthorityBoundaryFinding
canonicalToyFitAuthorityBoundaryFindings =
  ToyFitAuthorityBoundaryCurrentRoute.findings
    canonicalToyFitAuthorityBoundaryCurrentRoute
