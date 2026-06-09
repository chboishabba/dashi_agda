module DASHI.Physics.Closure.NextSessionInputRequestReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Manager C5 next-session input request receipt.
--
-- This receipt records only the three requested mathematical inputs for the
-- next session.  It supplies no Clay, CP/Vub, CKM, or terminal promotion.

data NextSessionInputRequestStatus : Set where
  nextSessionInputsRequestedNoPromotion :
    NextSessionInputRequestStatus

data NextSessionRequestedMathematicalInput : Set where
  clayYMSpatialRefinementInput :
    NextSessionRequestedMathematicalInput

  nsH74PrimeLPFlowPreservationInput :
    NextSessionRequestedMathematicalInput

  cpVubCMPeriodRatioArgumentInput :
    NextSessionRequestedMathematicalInput

canonicalNextSessionRequestedMathematicalInputs :
  List NextSessionRequestedMathematicalInput
canonicalNextSessionRequestedMathematicalInputs =
  clayYMSpatialRefinementInput
  ∷ nsH74PrimeLPFlowPreservationInput
  ∷ cpVubCMPeriodRatioArgumentInput
  ∷ []

clayYMSpatialRefinementRequest : String
clayYMSpatialRefinementRequest =
  "Clay YM input needed: a mechanism generating more than three spatial sites, namely a p-adic/adelic extension embedding Heegner points into a full 3D continuum."

nsH74PrimeLPFlowPreservationRequest : String
nsH74PrimeLPFlowPreservationRequest =
  "NS H74 input needed: a prime-LP flow preservation bound ||(1-Pi_d)(u dot grad u)||_{H^-1} <= epsilon_d with epsilon_d -> 0 and summable."

cpVubCMPeriodRatioArgumentRequest : String
cpVubCMPeriodRatioArgumentRequest =
  "CP/Vub input needed: a CM period ratio whose argument matches delta."

nextSessionInputRequestStatement : String
nextSessionInputRequestStatement =
  "Manager C5 records the three requested next-session mathematical inputs for Clay YM, NS H74, and CP/Vub; all promotion flags remain false."

data NextSessionInputRequestPromotion : Set where

nextSessionInputRequestPromotionImpossibleHere :
  NextSessionInputRequestPromotion →
  ⊥
nextSessionInputRequestPromotionImpossibleHere ()

record NextSessionInputRequestReceipt : Setω where
  field
    status :
      NextSessionInputRequestStatus

    requestedMathematicalInputs :
      List NextSessionRequestedMathematicalInput

    requestedMathematicalInputsAreCanonical :
      requestedMathematicalInputs
      ≡
      canonicalNextSessionRequestedMathematicalInputs

    clayYMInput :
      String

    clayYMInputIsCanonical :
      clayYMInput ≡ clayYMSpatialRefinementRequest

    clayYMMoreThanThreeSpatialSitesRequested :
      Bool

    clayYMMoreThanThreeSpatialSitesRequestedIsTrue :
      clayYMMoreThanThreeSpatialSitesRequested ≡ true

    clayYMPadicAdelicHeegnerTo3DContinuumRequested :
      Bool

    clayYMPadicAdelicHeegnerTo3DContinuumRequestedIsTrue :
      clayYMPadicAdelicHeegnerTo3DContinuumRequested ≡ true

    nsH74Input :
      String

    nsH74InputIsCanonical :
      nsH74Input ≡ nsH74PrimeLPFlowPreservationRequest

    nsH74PrimeLPFlowPreservationBoundRequested :
      Bool

    nsH74PrimeLPFlowPreservationBoundRequestedIsTrue :
      nsH74PrimeLPFlowPreservationBoundRequested ≡ true

    nsH74EpsilonSummableDecayRequested :
      Bool

    nsH74EpsilonSummableDecayRequestedIsTrue :
      nsH74EpsilonSummableDecayRequested ≡ true

    cpVubInput :
      String

    cpVubInputIsCanonical :
      cpVubInput ≡ cpVubCMPeriodRatioArgumentRequest

    cpVubCMPeriodRatioArgumentMatchesDeltaRequested :
      Bool

    cpVubCMPeriodRatioArgumentMatchesDeltaRequestedIsTrue :
      cpVubCMPeriodRatioArgumentMatchesDeltaRequested ≡ true

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    cpVubPromoted :
      Bool

    cpVubPromotedIsFalse :
      cpVubPromoted ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    promotionFlags :
      List NextSessionInputRequestPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ nextSessionInputRequestStatement

    receiptBoundary :
      List String

open NextSessionInputRequestReceipt public

canonicalNextSessionInputRequestReceipt :
  NextSessionInputRequestReceipt
canonicalNextSessionInputRequestReceipt =
  record
    { status =
        nextSessionInputsRequestedNoPromotion
    ; requestedMathematicalInputs =
        canonicalNextSessionRequestedMathematicalInputs
    ; requestedMathematicalInputsAreCanonical =
        refl
    ; clayYMInput =
        clayYMSpatialRefinementRequest
    ; clayYMInputIsCanonical =
        refl
    ; clayYMMoreThanThreeSpatialSitesRequested =
        true
    ; clayYMMoreThanThreeSpatialSitesRequestedIsTrue =
        refl
    ; clayYMPadicAdelicHeegnerTo3DContinuumRequested =
        true
    ; clayYMPadicAdelicHeegnerTo3DContinuumRequestedIsTrue =
        refl
    ; nsH74Input =
        nsH74PrimeLPFlowPreservationRequest
    ; nsH74InputIsCanonical =
        refl
    ; nsH74PrimeLPFlowPreservationBoundRequested =
        true
    ; nsH74PrimeLPFlowPreservationBoundRequestedIsTrue =
        refl
    ; nsH74EpsilonSummableDecayRequested =
        true
    ; nsH74EpsilonSummableDecayRequestedIsTrue =
        refl
    ; cpVubInput =
        cpVubCMPeriodRatioArgumentRequest
    ; cpVubInputIsCanonical =
        refl
    ; cpVubCMPeriodRatioArgumentMatchesDeltaRequested =
        true
    ; cpVubCMPeriodRatioArgumentMatchesDeltaRequestedIsTrue =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; cpVubPromoted =
        false
    ; cpVubPromotedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; statement =
        nextSessionInputRequestStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "This receipt records input requests only"
        ∷ "The Clay YM request is for spatial refinement beyond the three rigid Heegner sites"
        ∷ "The NS H74 request is for a summable prime-LP nonlinear leakage bound"
        ∷ "The CP/Vub request is for a CM period-ratio phase source matching delta"
        ∷ "No Clay, CP/Vub, CKM, or terminal promotion is asserted"
        ∷ []
    }

nextSessionInputRequestKeepsYMPromotionFalse :
  clayYangMillsPromoted canonicalNextSessionInputRequestReceipt ≡ false
nextSessionInputRequestKeepsYMPromotionFalse =
  refl

nextSessionInputRequestKeepsNSPromotionFalse :
  clayNavierStokesPromoted canonicalNextSessionInputRequestReceipt ≡ false
nextSessionInputRequestKeepsNSPromotionFalse =
  refl

nextSessionInputRequestKeepsCPVubPromotionFalse :
  cpVubPromoted canonicalNextSessionInputRequestReceipt ≡ false
nextSessionInputRequestKeepsCPVubPromotionFalse =
  refl

nextSessionInputRequestKeepsTerminalPromotionFalse :
  terminalClaimPromoted canonicalNextSessionInputRequestReceipt ≡ false
nextSessionInputRequestKeepsTerminalPromotionFalse =
  refl

nextSessionInputRequestNoPromotion :
  NextSessionInputRequestPromotion →
  ⊥
nextSessionInputRequestNoPromotion =
  nextSessionInputRequestPromotionImpossibleHere
