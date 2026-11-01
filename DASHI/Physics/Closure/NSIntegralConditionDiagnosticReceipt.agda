module DASHI.Physics.Closure.NSIntegralConditionDiagnosticReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- NS-C integral-condition diagnostic receipt.
--
-- This receipt records the weighted Qcrit integral route over the
-- lambda2 < 0, omega2, and S2/top enstrophy regions.  It explicitly keeps
-- the pointwise pressure route adverse on local N128 and does not promote
-- the integral route beyond diagnostic status.  External DNS data or an
-- analytic theorem is still required before any stronger claim can be made.

data NSIntegralConditionDiagnosticStatus : Set where
  weightedIntegralDiagnosticOnlyNoPromotion :
    NSIntegralConditionDiagnosticStatus

data NSIntegralConditionRoute : Set where
  weightedQcritIntegralOverLambda2Negative :
    NSIntegralConditionRoute

  weightedQcritIntegralOverOmega2 :
    NSIntegralConditionRoute

  weightedQcritIntegralOverS2TopEnstrophy :
    NSIntegralConditionRoute

  pressurePointwiseRouteAdverseOnLocalN128Route :
    NSIntegralConditionRoute

  externalDNSStillRequired :
    NSIntegralConditionRoute

  analyticTheoremStillRequired :
    NSIntegralConditionRoute

canonicalNSIntegralConditionRoute :
  List NSIntegralConditionRoute
canonicalNSIntegralConditionRoute =
  weightedQcritIntegralOverLambda2Negative
  ∷ weightedQcritIntegralOverOmega2
  ∷ weightedQcritIntegralOverS2TopEnstrophy
  ∷ pressurePointwiseRouteAdverseOnLocalN128Route
  ∷ externalDNSStillRequired
  ∷ analyticTheoremStillRequired
  ∷ []

data NSIntegralConditionPromotion : Set where

nsIntegralConditionPromotionImpossibleHere :
  NSIntegralConditionPromotion →
  ⊥
nsIntegralConditionPromotionImpossibleHere ()

nsIntegralConditionDiagnosticStatement : String
nsIntegralConditionDiagnosticStatement =
  "NS-C integral-condition diagnostic: record the weighted Qcrit integral route over lambda2 < 0, omega2, and S2/top enstrophy regions; keep the pressure pointwise route adverse on local N128; and leave the integral route diagnostic-only pending external DNS or an analytic theorem. No promotion and no Clay claim."

record NSIntegralConditionDiagnosticORCSLPGF : Set where
  constructor nsIntegralConditionDiagnosticORCSLPGF
  field
    O : String
    OIsCanonical : O ≡
      "O: Record the NS-C integral-condition diagnostic route as a fail-closed receipt."

    R : String
    RIsCanonical : R ≡
      "R: Record weighted Qcrit integrals over lambda2 < 0, omega2, and S2/top enstrophy regions; keep the pointwise pressure route adverse on local N128; and require external DNS or an analytic theorem before any stronger claim."

    C : String
    CIsCanonical : C ≡
      "C: The Agda artifact exports the canonical integral route list, fail-closed status, diagnostic statement, and promotion blocker."

    S : String
    SIsCanonical : S ≡
      "S: weightedQcritIntegralOverLambda2Negative=true; weightedQcritIntegralOverOmega2=true; weightedQcritIntegralOverS2TopEnstrophy=true; pressurePointwiseRouteAdverseOnLocalN128=true; externalDNSStillRequired=true; analyticTheoremStillRequired=true; integralRouteDiagnosticOnly=true; clayPromotion=false."

    L : String
    LIsCanonical : L ≡
      "L: lambda2 < 0, omega2, and S2/top enstrophy integral diagnostics sit above the pressure pointwise lane, while external DNS or an analytic theorem remains the missing bridge."

    P : String
    PIsCanonical : P ≡
      "P: Keep the route diagnostic-only and wait for external DNS or a formal analytic theorem before revisiting any closure claim."

    G : String
    GIsCanonical : G ≡
      "G: No promotion, no Clay claim, and no reinterpretation of the pressure pointwise failure as support for closure."

    F : String
    FIsCanonical : F ≡
      "F: The integral-condition route remains fail-closed because the pointwise pressure lane is adverse on local N128 and the external DNS/analytic theorem input is still absent."

record NSIntegralConditionDiagnosticReceipt : Setω where
  field
    status :
      NSIntegralConditionDiagnosticStatus

    statusIsCanonical :
      status ≡ weightedIntegralDiagnosticOnlyNoPromotion

    route :
      List NSIntegralConditionRoute

    routeIsCanonical :
      route ≡ canonicalNSIntegralConditionRoute

    weightedQcritIntegralOverLambda2NegativeRecorded :
      Bool

    weightedQcritIntegralOverLambda2NegativeRecordedIsTrue :
      weightedQcritIntegralOverLambda2NegativeRecorded ≡ true

    weightedQcritIntegralOverOmega2Recorded :
      Bool

    weightedQcritIntegralOverOmega2RecordedIsTrue :
      weightedQcritIntegralOverOmega2Recorded ≡ true

    weightedQcritIntegralOverS2TopEnstrophyRecorded :
      Bool

    weightedQcritIntegralOverS2TopEnstrophyRecordedIsTrue :
      weightedQcritIntegralOverS2TopEnstrophyRecorded ≡ true

    pressurePointwiseRouteAdverseOnLocalN128 :
      Bool

    pressurePointwiseRouteAdverseOnLocalN128IsTrue :
      pressurePointwiseRouteAdverseOnLocalN128 ≡ true

    externalDNSRequired :
      Bool

    externalDNSRequiredIsTrue :
      externalDNSRequired ≡ true

    analyticTheoremRequired :
      Bool

    analyticTheoremRequiredIsTrue :
      analyticTheoremRequired ≡ true

    integralRouteDiagnosticOnly :
      Bool

    integralRouteDiagnosticOnlyIsTrue :
      integralRouteDiagnosticOnly ≡ true

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    integralConditionStatement :
      String

    integralConditionStatementIsCanonical :
      integralConditionStatement ≡ nsIntegralConditionDiagnosticStatement

    orcslpgf :
      NSIntegralConditionDiagnosticORCSLPGF

open NSIntegralConditionDiagnosticReceipt public

canonicalNSIntegralConditionDiagnosticORCSLPGF :
  NSIntegralConditionDiagnosticORCSLPGF
canonicalNSIntegralConditionDiagnosticORCSLPGF =
  nsIntegralConditionDiagnosticORCSLPGF
    "O: Record the NS-C integral-condition diagnostic route as a fail-closed receipt."
    refl
    "R: Record weighted Qcrit integrals over lambda2 < 0, omega2, and S2/top enstrophy regions; keep the pointwise pressure route adverse on local N128; and require external DNS or an analytic theorem before any stronger claim."
    refl
    "C: The Agda artifact exports the canonical integral route list, fail-closed status, diagnostic statement, and promotion blocker."
    refl
    "S: weightedQcritIntegralOverLambda2Negative=true; weightedQcritIntegralOverOmega2=true; weightedQcritIntegralOverS2TopEnstrophy=true; pressurePointwiseRouteAdverseOnLocalN128=true; externalDNSStillRequired=true; analyticTheoremStillRequired=true; integralRouteDiagnosticOnly=true; clayPromotion=false."
    refl
    "L: lambda2 < 0, omega2, and S2/top enstrophy integral diagnostics sit above the pressure pointwise lane, while external DNS or an analytic theorem remains the missing bridge."
    refl
    "P: Keep the route diagnostic-only and wait for external DNS or a formal analytic theorem before revisiting any closure claim."
    refl
    "G: No promotion, no Clay claim, and no reinterpretation of the pressure pointwise failure as support for closure."
    refl
    "F: The integral-condition route remains fail-closed because the pointwise pressure lane is adverse on local N128 and the external DNS/analytic theorem input is still absent."
    refl

canonicalNSIntegralConditionDiagnosticReceipt :
  NSIntegralConditionDiagnosticReceipt
canonicalNSIntegralConditionDiagnosticReceipt =
  record
    { status =
        weightedIntegralDiagnosticOnlyNoPromotion
    ; statusIsCanonical =
        refl
    ; route =
        canonicalNSIntegralConditionRoute
    ; routeIsCanonical =
        refl
    ; weightedQcritIntegralOverLambda2NegativeRecorded =
        true
    ; weightedQcritIntegralOverLambda2NegativeRecordedIsTrue =
        refl
    ; weightedQcritIntegralOverOmega2Recorded =
        true
    ; weightedQcritIntegralOverOmega2RecordedIsTrue =
        refl
    ; weightedQcritIntegralOverS2TopEnstrophyRecorded =
        true
    ; weightedQcritIntegralOverS2TopEnstrophyRecordedIsTrue =
        refl
    ; pressurePointwiseRouteAdverseOnLocalN128 =
        true
    ; pressurePointwiseRouteAdverseOnLocalN128IsTrue =
        refl
    ; externalDNSRequired =
        true
    ; externalDNSRequiredIsTrue =
        refl
    ; analyticTheoremRequired =
        true
    ; analyticTheoremRequiredIsTrue =
        refl
    ; integralRouteDiagnosticOnly =
        true
    ; integralRouteDiagnosticOnlyIsTrue =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; integralConditionStatement =
        nsIntegralConditionDiagnosticStatement
    ; integralConditionStatementIsCanonical =
        refl
    ; orcslpgf =
        canonicalNSIntegralConditionDiagnosticORCSLPGF
    }
