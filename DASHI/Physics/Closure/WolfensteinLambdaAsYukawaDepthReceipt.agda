module DASHI.Physics.Closure.WolfensteinLambdaAsYukawaDepthReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CabibboAngleCarrierReceipt as Cabibbo
import DASHI.Physics.Closure.WolfensteinLambdaAFromCarrierReceipt as WolfLambdaA

------------------------------------------------------------------------
-- Wolfenstein lambda as down-type 1-2 Yukawa depth receipt.
--
-- This receipt records a structural unification only:
--
--   lambda = |V_us| = sqrt(m_d / m_s)
--
-- at the carrier-depth surface.  The statement is not promoted to a
-- terminal, physical, or Clay result.  Its use here is to mark the
-- Georgi-Jarlskog numerical coincidence as a same-carrier-depth-separation
-- candidate rather than an independent physical derivation.

data StructuralUnificationStatus : Set where
  structural :
    StructuralUnificationStatus

data CoincidenceExplanation : Set where
  sameCarrierDepthSeparation :
    CoincidenceExplanation

data CarrierExplanationStatus : Set where
  candidate :
    CarrierExplanationStatus

data WolfensteinLambdaAsYukawaDepthStatus : Set where
  wolfensteinLambdaYukawaDepthUnificationRecorded :
    WolfensteinLambdaAsYukawaDepthStatus

data WolfensteinLambdaAsYukawaDepthBlocker : Set where
  missingPhysicalDownMassAuthority :
    WolfensteinLambdaAsYukawaDepthBlocker

  missingRunningScaleAndSchemeBinding :
    WolfensteinLambdaAsYukawaDepthBlocker

  missingAcceptedPDGWolfensteinBinding :
    WolfensteinLambdaAsYukawaDepthBlocker

  missingGeorgiJarlskogTheoremAuthority :
    WolfensteinLambdaAsYukawaDepthBlocker

canonicalWolfensteinLambdaAsYukawaDepthBlockers :
  List WolfensteinLambdaAsYukawaDepthBlocker
canonicalWolfensteinLambdaAsYukawaDepthBlockers =
  missingPhysicalDownMassAuthority
  ∷ missingRunningScaleAndSchemeBinding
  ∷ missingAcceptedPDGWolfensteinBinding
  ∷ missingGeorgiJarlskogTheoremAuthority
  ∷ []

data WolfensteinLambdaAsYukawaDepthPromotion : Set where

wolfensteinLambdaAsYukawaDepthPromotionImpossibleHere :
  WolfensteinLambdaAsYukawaDepthPromotion →
  ⊥
wolfensteinLambdaAsYukawaDepthPromotionImpossibleHere ()

wolfensteinCabibboCarrierLabel : String
wolfensteinCabibboCarrierLabel =
  "lambda is the Cabibbo angle |V_us| at the carrier surface"

downTwelveDepthSeparationLabel : String
downTwelveDepthSeparationLabel =
  "lambda is the down-type 1-2 Yukawa depth separation sqrt(m_d/m_s)"

georgiJarlskogCarrierCoincidenceLabel : String
georgiJarlskogCarrierCoincidenceLabel =
  "Georgi-Jarlskog coincidence is same carrier depth separation"

record WolfensteinLambdaAsYukawaDepthReceipt : Setω where
  field
    status :
      WolfensteinLambdaAsYukawaDepthStatus

    cabibboReceipt :
      Cabibbo.CabibboAngleCarrierReceipt

    cabibboReceiptIsCanonical :
      Bool

    cabibboReceiptIsCanonicalIsTrue :
      cabibboReceiptIsCanonical ≡ true

    wolfensteinLambdaReceipt :
      WolfLambdaA.WolfensteinLambdaAFromCarrierReceipt

    wolfensteinLambdaReceiptIsCanonical :
      Bool

    wolfensteinLambdaReceiptIsCanonicalIsTrue :
      wolfensteinLambdaReceiptIsCanonical ≡ true

    lambdaAsCabibboAngle :
      String

    lambdaAsCabibboAngleIsCanonical :
      lambdaAsCabibboAngle ≡ wolfensteinCabibboCarrierLabel

    lambdaAsDownTwelveYukawaDepth :
      String

    lambdaAsDownTwelveYukawaDepthIsCanonical :
      lambdaAsDownTwelveYukawaDepth ≡ downTwelveDepthSeparationLabel

    structuralUnificationRecorded :
      Bool

    structuralUnificationRecordedIsTrue :
      structuralUnificationRecorded ≡ true

    wolfensteinLambdaEqualsAlphaD :
      StructuralUnificationStatus

    wolfensteinLambdaEqualsAlphaDIsStructural :
      wolfensteinLambdaEqualsAlphaD ≡ structural

    georgiJarlskogFromCarrier :
      Bool

    georgiJarlskogFromCarrierIsTrue :
      georgiJarlskogFromCarrier ≡ true

    explanationOfCoincidence :
      CoincidenceExplanation

    explanationOfCoincidenceIsSameCarrierDepthSeparation :
      explanationOfCoincidence ≡ sameCarrierDepthSeparation

    georgiJarlskogExplainedByCarrier :
      CarrierExplanationStatus

    georgiJarlskogExplainedByCarrierIsCandidate :
      georgiJarlskogExplainedByCarrier ≡ candidate

    georgiJarlskogCoincidenceLabel :
      String

    georgiJarlskogCoincidenceLabelIsCanonical :
      georgiJarlskogCoincidenceLabel
      ≡
      georgiJarlskogCarrierCoincidenceLabel

    physicalPromotionConstructed :
      Bool

    physicalPromotionConstructedIsFalse :
      physicalPromotionConstructed ≡ false

    terminalPromotionConstructed :
      Bool

    terminalPromotionConstructedIsFalse :
      terminalPromotionConstructed ≡ false

    clayPromotionConstructed :
      Bool

    clayPromotionConstructedIsFalse :
      clayPromotionConstructed ≡ false

    blockers :
      List WolfensteinLambdaAsYukawaDepthBlocker

    blockersAreCanonical :
      blockers ≡ canonicalWolfensteinLambdaAsYukawaDepthBlockers

    promotionFlags :
      List WolfensteinLambdaAsYukawaDepthPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open WolfensteinLambdaAsYukawaDepthReceipt public

canonicalWolfensteinLambdaAsYukawaDepthReceipt :
  WolfensteinLambdaAsYukawaDepthReceipt
canonicalWolfensteinLambdaAsYukawaDepthReceipt =
  record
    { status =
        wolfensteinLambdaYukawaDepthUnificationRecorded
    ; cabibboReceipt =
        Cabibbo.canonicalCabibboAngleCarrierReceipt
    ; cabibboReceiptIsCanonical =
        true
    ; cabibboReceiptIsCanonicalIsTrue =
        refl
    ; wolfensteinLambdaReceipt =
        WolfLambdaA.canonicalWolfensteinLambdaAFromCarrierReceipt
    ; wolfensteinLambdaReceiptIsCanonical =
        true
    ; wolfensteinLambdaReceiptIsCanonicalIsTrue =
        refl
    ; lambdaAsCabibboAngle =
        wolfensteinCabibboCarrierLabel
    ; lambdaAsCabibboAngleIsCanonical =
        refl
    ; lambdaAsDownTwelveYukawaDepth =
        downTwelveDepthSeparationLabel
    ; lambdaAsDownTwelveYukawaDepthIsCanonical =
        refl
    ; structuralUnificationRecorded =
        true
    ; structuralUnificationRecordedIsTrue =
        refl
    ; wolfensteinLambdaEqualsAlphaD =
        structural
    ; wolfensteinLambdaEqualsAlphaDIsStructural =
        refl
    ; georgiJarlskogFromCarrier =
        true
    ; georgiJarlskogFromCarrierIsTrue =
        refl
    ; explanationOfCoincidence =
        sameCarrierDepthSeparation
    ; explanationOfCoincidenceIsSameCarrierDepthSeparation =
        refl
    ; georgiJarlskogExplainedByCarrier =
        candidate
    ; georgiJarlskogExplainedByCarrierIsCandidate =
        refl
    ; georgiJarlskogCoincidenceLabel =
        georgiJarlskogCarrierCoincidenceLabel
    ; georgiJarlskogCoincidenceLabelIsCanonical =
        refl
    ; physicalPromotionConstructed =
        false
    ; physicalPromotionConstructedIsFalse =
        refl
    ; terminalPromotionConstructed =
        false
    ; terminalPromotionConstructedIsFalse =
        refl
    ; clayPromotionConstructed =
        false
    ; clayPromotionConstructedIsFalse =
        refl
    ; blockers =
        canonicalWolfensteinLambdaAsYukawaDepthBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Structural unification recorded: Wolfenstein lambda is both |V_us| and sqrt(m_d/m_s) as a down-type 1-2 carrier-depth separation"
        ∷ "wolfensteinLambdaEqualsAlphaD=structural records the shared carrier-depth role"
        ∷ "georgiJarlskogFromCarrier=true records the Georgi-Jarlskog coincidence as carrier-visible"
        ∷ "explanationOfCoincidence=sameCarrierDepthSeparation and georgiJarlskogExplainedByCarrier=candidate keep the explanation structural, not promoted"
        ∷ "Physical, terminal, and Clay promotions remain false"
        ∷ []
    }

wolfensteinLambdaEqualsAlphaDIsStructuralReceipt :
  wolfensteinLambdaEqualsAlphaD
    canonicalWolfensteinLambdaAsYukawaDepthReceipt
  ≡
  structural
wolfensteinLambdaEqualsAlphaDIsStructuralReceipt =
  refl

georgiJarlskogFromCarrierTrueReceipt :
  georgiJarlskogFromCarrier
    canonicalWolfensteinLambdaAsYukawaDepthReceipt
  ≡
  true
georgiJarlskogFromCarrierTrueReceipt =
  refl

georgiJarlskogExplainedByCarrierCandidateReceipt :
  georgiJarlskogExplainedByCarrier
    canonicalWolfensteinLambdaAsYukawaDepthReceipt
  ≡
  candidate
georgiJarlskogExplainedByCarrierCandidateReceipt =
  refl

wolfensteinLambdaAsYukawaDepthKeepsPhysicalPromotionFalse :
  physicalPromotionConstructed
    canonicalWolfensteinLambdaAsYukawaDepthReceipt
  ≡
  false
wolfensteinLambdaAsYukawaDepthKeepsPhysicalPromotionFalse =
  refl

wolfensteinLambdaAsYukawaDepthKeepsTerminalPromotionFalse :
  terminalPromotionConstructed
    canonicalWolfensteinLambdaAsYukawaDepthReceipt
  ≡
  false
wolfensteinLambdaAsYukawaDepthKeepsTerminalPromotionFalse =
  refl

wolfensteinLambdaAsYukawaDepthKeepsClayPromotionFalse :
  clayPromotionConstructed
    canonicalWolfensteinLambdaAsYukawaDepthReceipt
  ≡
  false
wolfensteinLambdaAsYukawaDepthKeepsClayPromotionFalse =
  refl
