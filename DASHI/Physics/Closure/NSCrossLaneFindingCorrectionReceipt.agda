module DASHI.Physics.Closure.NSCrossLaneFindingCorrectionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Manager C1: Navier-Stokes cross-lane finding correction receipt.
--
-- This receipt corrects the prior NSCrossLaneSuppressionReceipt finding.
-- The prior claim that cross-lane interactions are suppressed because their
-- outputs are off carrier was too strong: exact low-band landings exist.
--
-- Examples:
--
--   |2^1 - 3^2| = 7
--   |3^4 - 7^2| = 32
--
-- The corrected finding is not that cross-lane terms are absent.  It is that
-- Thue-Mahler type finiteness makes such exact landings finite per fixed
-- output band, so the cross-lane contribution is recorded as bounded forcing
-- rather than a feedback cascade.  The candidate global bound survives as a
-- bounded-forcing statement, but it requires a follow-up audit in the A2
-- receipt.  No Clay promotion is made here.

data PriorCrossLaneReceipt : Set where
  nsCrossLaneSuppressionReceipt :
    PriorCrossLaneReceipt

data CrossLaneFindingCorrectionStatus : Set where
  managerC1Correction :
    CrossLaneFindingCorrectionStatus

  priorSuppressionClaimWasWrong :
    CrossLaneFindingCorrectionStatus

  exactLowBandLandingsExist :
    CrossLaneFindingCorrectionStatus

  thueMahlerFinitenessPerBand :
    CrossLaneFindingCorrectionStatus

  boundedForcingNotFeedback :
    CrossLaneFindingCorrectionStatus

  globalBoundSurvivesAsBoundedForcing :
    CrossLaneFindingCorrectionStatus

  auditRequiredInA2Receipt :
    CrossLaneFindingCorrectionStatus

  clayPromotionFlagsRemainFalse :
    CrossLaneFindingCorrectionStatus

canonicalCrossLaneFindingCorrectionStatus :
  List CrossLaneFindingCorrectionStatus
canonicalCrossLaneFindingCorrectionStatus =
  managerC1Correction
  ∷ priorSuppressionClaimWasWrong
  ∷ exactLowBandLandingsExist
  ∷ thueMahlerFinitenessPerBand
  ∷ boundedForcingNotFeedback
  ∷ globalBoundSurvivesAsBoundedForcing
  ∷ auditRequiredInA2Receipt
  ∷ clayPromotionFlagsRemainFalse
  ∷ []

data LowBandLandingExample : Set where
  twoPowerOneMinusThreePowerTwoLandsAtSeven :
    LowBandLandingExample

  threePowerFourMinusSevenPowerTwoLandsAtThirtyTwo :
    LowBandLandingExample

canonicalLowBandLandingExamples :
  List LowBandLandingExample
canonicalLowBandLandingExamples =
  twoPowerOneMinusThreePowerTwoLandsAtSeven
  ∷ threePowerFourMinusSevenPowerTwoLandsAtThirtyTwo
  ∷ []

data CrossLaneTermRole : Set where
  boundedForcing :
    CrossLaneTermRole

  feedbackCascade :
    CrossLaneTermRole

data CrossLaneArithmeticControl : Set where
  thueMahlerFiniteExactLandingsPerBand :
    CrossLaneArithmeticControl

data FollowUpAuditReceipt : Set where
  a2Receipt :
    FollowUpAuditReceipt

data NSCrossLaneFindingCorrectionPromotion : Set where

nsCrossLaneFindingCorrectionPromotionImpossibleHere :
  NSCrossLaneFindingCorrectionPromotion →
  ⊥
nsCrossLaneFindingCorrectionPromotionImpossibleHere ()

exampleSevenFormula :
  String
exampleSevenFormula =
  "|2^1 - 3^2| = 7"

exampleThirtyTwoFormula :
  String
exampleThirtyTwoFormula =
  "|3^4 - 7^2| = 32"

nsCrossLaneFindingCorrectionStatement :
  String
nsCrossLaneFindingCorrectionStatement =
  "C1 correction: the prior NSCrossLaneSuppressionReceipt claim that cross-lane outputs are suppressed/off-carrier was wrong. Exact low-band landings exist, including |2^1 - 3^2| = 7 and |3^4 - 7^2| = 32. Thue-Mahler finiteness makes exact landings finite per fixed output band, so the cross-lane term is bounded forcing rather than feedback. The global bound survives in that bounded-forcing form, with audit required in the A2 receipt. All Clay promotion flags remain false."

record NSCrossLaneFindingCorrectionReceipt : Setω where
  field
    correctedPriorReceipt :
      PriorCrossLaneReceipt

    correctedPriorReceiptIsSuppression :
      correctedPriorReceipt ≡ nsCrossLaneSuppressionReceipt

    status :
      List CrossLaneFindingCorrectionStatus

    statusIsCanonical :
      status ≡ canonicalCrossLaneFindingCorrectionStatus

    priorCrossLaneSuppressedClaimWasWrong :
      Bool

    priorCrossLaneSuppressedClaimWasWrongIsTrue :
      priorCrossLaneSuppressedClaimWasWrong ≡ true

    exactLowBandLandingsExistFlag :
      Bool

    exactLowBandLandingsExistFlagIsTrue :
      exactLowBandLandingsExistFlag ≡ true

    examples :
      List LowBandLandingExample

    examplesAreCanonical :
      examples ≡ canonicalLowBandLandingExamples

    firstLandingFormula :
      String

    firstLandingFormulaIsCanonical :
      firstLandingFormula ≡ exampleSevenFormula

    firstLandingValue :
      Nat

    firstLandingValueIsSeven :
      firstLandingValue ≡ 7

    secondLandingFormula :
      String

    secondLandingFormulaIsCanonical :
      secondLandingFormula ≡ exampleThirtyTwoFormula

    secondLandingValue :
      Nat

    secondLandingValueIsThirtyTwo :
      secondLandingValue ≡ 32

    arithmeticControl :
      CrossLaneArithmeticControl

    arithmeticControlIsThueMahler :
      arithmeticControl ≡ thueMahlerFiniteExactLandingsPerBand

    finiteExactLandingsPerBand :
      Bool

    finiteExactLandingsPerBandIsTrue :
      finiteExactLandingsPerBand ≡ true

    crossLaneTermRole :
      CrossLaneTermRole

    crossLaneTermRoleIsBoundedForcing :
      crossLaneTermRole ≡ boundedForcing

    crossLaneTermIsFeedback :
      Bool

    crossLaneTermIsFeedbackIsFalse :
      crossLaneTermIsFeedback ≡ false

    globalBoundSurvives :
      Bool

    globalBoundSurvivesIsTrue :
      globalBoundSurvives ≡ true

    auditRequired :
      FollowUpAuditReceipt

    auditRequiredIsA2Receipt :
      auditRequired ≡ a2Receipt

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    globalRegularityPromoted :
      Bool

    globalRegularityPromotedIsFalse :
      globalRegularityPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    promotionFlags :
      List NSCrossLaneFindingCorrectionPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ nsCrossLaneFindingCorrectionStatement

    receiptBoundary :
      List String

open NSCrossLaneFindingCorrectionReceipt public

canonicalNSCrossLaneFindingCorrectionReceipt :
  NSCrossLaneFindingCorrectionReceipt
canonicalNSCrossLaneFindingCorrectionReceipt =
  record
    { correctedPriorReceipt =
        nsCrossLaneSuppressionReceipt
    ; correctedPriorReceiptIsSuppression =
        refl
    ; status =
        canonicalCrossLaneFindingCorrectionStatus
    ; statusIsCanonical =
        refl
    ; priorCrossLaneSuppressedClaimWasWrong =
        true
    ; priorCrossLaneSuppressedClaimWasWrongIsTrue =
        refl
    ; exactLowBandLandingsExistFlag =
        true
    ; exactLowBandLandingsExistFlagIsTrue =
        refl
    ; examples =
        canonicalLowBandLandingExamples
    ; examplesAreCanonical =
        refl
    ; firstLandingFormula =
        exampleSevenFormula
    ; firstLandingFormulaIsCanonical =
        refl
    ; firstLandingValue =
        7
    ; firstLandingValueIsSeven =
        refl
    ; secondLandingFormula =
        exampleThirtyTwoFormula
    ; secondLandingFormulaIsCanonical =
        refl
    ; secondLandingValue =
        32
    ; secondLandingValueIsThirtyTwo =
        refl
    ; arithmeticControl =
        thueMahlerFiniteExactLandingsPerBand
    ; arithmeticControlIsThueMahler =
        refl
    ; finiteExactLandingsPerBand =
        true
    ; finiteExactLandingsPerBandIsTrue =
        refl
    ; crossLaneTermRole =
        boundedForcing
    ; crossLaneTermRoleIsBoundedForcing =
        refl
    ; crossLaneTermIsFeedback =
        false
    ; crossLaneTermIsFeedbackIsFalse =
        refl
    ; globalBoundSurvives =
        true
    ; globalBoundSurvivesIsTrue =
        refl
    ; auditRequired =
        a2Receipt
    ; auditRequiredIsA2Receipt =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; globalRegularityPromoted =
        false
    ; globalRegularityPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; statement =
        nsCrossLaneFindingCorrectionStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "Corrects prior NSCrossLaneSuppressionReceipt"
        ∷ "Prior claim cross-lane suppressed was wrong"
        ∷ "Exact low-band landings exist: |2^1 - 3^2| = 7"
        ∷ "Exact low-band landings exist: |3^4 - 7^2| = 32"
        ∷ "Thue-Mahler finiteness records finite exact landings per fixed output band"
        ∷ "Cross-lane term is bounded forcing, not feedback"
        ∷ "Global bound survives as bounded forcing"
        ∷ "A2 receipt audit required"
        ∷ "All Clay promotion flags remain false"
        ∷ []
    }

nsCrossLaneFindingCorrectionPriorClaimWasWrong :
  priorCrossLaneSuppressedClaimWasWrong
    canonicalNSCrossLaneFindingCorrectionReceipt
  ≡
  true
nsCrossLaneFindingCorrectionPriorClaimWasWrong =
  refl

nsCrossLaneFindingCorrectionExactLowBandLandingsExist :
  exactLowBandLandingsExistFlag
    canonicalNSCrossLaneFindingCorrectionReceipt
  ≡
  true
nsCrossLaneFindingCorrectionExactLowBandLandingsExist =
  refl

nsCrossLaneFindingCorrectionBoundedForcingNotFeedback :
  crossLaneTermRole canonicalNSCrossLaneFindingCorrectionReceipt
  ≡
  boundedForcing
nsCrossLaneFindingCorrectionBoundedForcingNotFeedback =
  refl

nsCrossLaneFindingCorrectionGlobalBoundSurvives :
  globalBoundSurvives canonicalNSCrossLaneFindingCorrectionReceipt
  ≡
  true
nsCrossLaneFindingCorrectionGlobalBoundSurvives =
  refl

nsCrossLaneFindingCorrectionAuditRequiredInA2 :
  auditRequired canonicalNSCrossLaneFindingCorrectionReceipt
  ≡
  a2Receipt
nsCrossLaneFindingCorrectionAuditRequiredInA2 =
  refl

nsCrossLaneFindingCorrectionDoesNotPromoteClay :
  clayNavierStokesPromoted canonicalNSCrossLaneFindingCorrectionReceipt
  ≡
  false
nsCrossLaneFindingCorrectionDoesNotPromoteClay =
  refl

nsCrossLaneFindingCorrectionDoesNotPromoteGlobalRegularity :
  globalRegularityPromoted canonicalNSCrossLaneFindingCorrectionReceipt
  ≡
  false
nsCrossLaneFindingCorrectionDoesNotPromoteGlobalRegularity =
  refl

nsCrossLaneFindingCorrectionDoesNotPromoteTerminalClay :
  terminalClayClaimPromoted canonicalNSCrossLaneFindingCorrectionReceipt
  ≡
  false
nsCrossLaneFindingCorrectionDoesNotPromoteTerminalClay =
  refl
