module DASHI.Physics.Closure.NSCarrierFrequencyProgrammeStatusReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSFinalStateReceipt as Final
import DASHI.Physics.Closure.NSVorticityNoMechanismReceipt as Vorticity

data NSCarrierFrequencyProgrammeStatus : Set where
  finalTrancheStatusRecordedWithoutClayPromotion :
    NSCarrierFrequencyProgrammeStatus

data NSCarrierFrequencyProgrammeObservation : Set where
  adjacentOnlyArithmeticObservationInteresting :
    NSCarrierFrequencyProgrammeObservation

  h74RouteConditionalOnFourierRestriction :
    NSCarrierFrequencyProgrammeObservation

  exactPrimeLPFlowInvarianceBlockedObservation :
    NSCarrierFrequencyProgrammeObservation

  separateCascadeConservationUnprovedObservation :
    NSCarrierFrequencyProgrammeObservation

  pillaiRouteSpeculativeObservation :
    NSCarrierFrequencyProgrammeObservation

  unrestrictedClayNSFalseObservation :
    NSCarrierFrequencyProgrammeObservation

canonicalNSCarrierFrequencyProgrammeObservations :
  List NSCarrierFrequencyProgrammeObservation
canonicalNSCarrierFrequencyProgrammeObservations =
  adjacentOnlyArithmeticObservationInteresting
  ∷ h74RouteConditionalOnFourierRestriction
  ∷ exactPrimeLPFlowInvarianceBlockedObservation
  ∷ separateCascadeConservationUnprovedObservation
  ∷ pillaiRouteSpeculativeObservation
  ∷ unrestrictedClayNSFalseObservation
  ∷ []

data NSCarrierFrequencyProgrammePromotion : Set where

nsCarrierFrequencyProgrammePromotionImpossibleHere :
  NSCarrierFrequencyProgrammePromotion →
  ⊥
nsCarrierFrequencyProgrammePromotionImpossibleHere ()

nsCarrierFrequencyProgrammeStatement : String
nsCarrierFrequencyProgrammeStatement =
  "Final tranche status: adjacent-only arithmetic is interesting; the H74 route is conditional on a missing Fourier restriction theorem; exact prime-LP flow invariance, separate cascade conservation, and unrestricted Clay NS remain unproved or false; the Pillai route is speculative."

canonicalNSCarrierFrequencyNextInput : String
canonicalNSCarrierFrequencyNextInput =
  "proof or counterexample for H74 restricted carrier data"

record NSCarrierFrequencyProgrammeStatusReceipt : Setω where
  field
    status :
      NSCarrierFrequencyProgrammeStatus

    finalStateReceipt :
      Final.NSFinalStateReceipt

    finalStateClayFalse :
      Final.clayNavierStokesPromoted finalStateReceipt ≡ false

    vorticityNoMechanismReceipt :
      Vorticity.NSVorticityNoMechanismReceipt

    vorticityMechanismAbsent :
      Vorticity.carrierVorticityMechanismConstructed
        vorticityNoMechanismReceipt
      ≡
      false

    observations :
      List NSCarrierFrequencyProgrammeObservation

    observationsAreCanonical :
      observations ≡ canonicalNSCarrierFrequencyProgrammeObservations

    adjacentOnlyObservationRecorded :
      Bool

    adjacentOnlyObservationRecordedIsTrue :
      adjacentOnlyObservationRecorded ≡ true

    option1MostTractable :
      Bool

    option1MostTractableIsTrue :
      option1MostTractable ≡ true

    h74RouteConditional :
      Bool

    h74RouteConditionalIsTrue :
      h74RouteConditional ≡ true

    fourierRestrictionTheoremSupplied :
      Bool

    fourierRestrictionTheoremSuppliedIsFalse :
      fourierRestrictionTheoremSupplied ≡ false

    exactPrimeLPFlowInvarianceProved :
      Bool

    exactPrimeLPFlowInvarianceProvedIsFalse :
      exactPrimeLPFlowInvarianceProved ≡ false

    exactPrimeLPFlowInvarianceBlocked :
      Bool

    exactPrimeLPFlowInvarianceBlockedIsTrue :
      exactPrimeLPFlowInvarianceBlocked ≡ true

    separateCascadeConservationProved :
      Bool

    separateCascadeConservationProvedIsFalse :
      separateCascadeConservationProved ≡ false

    pillaiRouteSpeculative :
      Bool

    pillaiRouteSpeculativeIsTrue :
      pillaiRouteSpeculative ≡ true

    unrestrictedClayNSRemainsFalse :
      Bool

    unrestrictedClayNSRemainsFalseIsTrue :
      unrestrictedClayNSRemainsFalse ≡ true

    nsClayPromoted :
      Bool

    nsClayPromotedIsFalse :
      nsClayPromoted ≡ false

    nextInputNeeded :
      String

    nextInputNeededIsCanonical :
      nextInputNeeded ≡ canonicalNSCarrierFrequencyNextInput

    statement :
      String

    statementIsCanonical :
      statement ≡ nsCarrierFrequencyProgrammeStatement

    promotionFlags :
      List NSCarrierFrequencyProgrammePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSCarrierFrequencyProgrammeStatusReceipt public

canonicalNSCarrierFrequencyProgrammeStatusReceipt :
  NSCarrierFrequencyProgrammeStatusReceipt
canonicalNSCarrierFrequencyProgrammeStatusReceipt =
  record
    { status =
        finalTrancheStatusRecordedWithoutClayPromotion
    ; finalStateReceipt =
        Final.canonicalNSFinalStateReceipt
    ; finalStateClayFalse =
        refl
    ; vorticityNoMechanismReceipt =
        Vorticity.canonicalNSVorticityNoMechanismReceipt
    ; vorticityMechanismAbsent =
        refl
    ; observations =
        canonicalNSCarrierFrequencyProgrammeObservations
    ; observationsAreCanonical =
        refl
    ; adjacentOnlyObservationRecorded =
        true
    ; adjacentOnlyObservationRecordedIsTrue =
        refl
    ; option1MostTractable =
        true
    ; option1MostTractableIsTrue =
        refl
    ; h74RouteConditional =
        true
    ; h74RouteConditionalIsTrue =
        refl
    ; fourierRestrictionTheoremSupplied =
        false
    ; fourierRestrictionTheoremSuppliedIsFalse =
        refl
    ; exactPrimeLPFlowInvarianceProved =
        false
    ; exactPrimeLPFlowInvarianceProvedIsFalse =
        refl
    ; exactPrimeLPFlowInvarianceBlocked =
        true
    ; exactPrimeLPFlowInvarianceBlockedIsTrue =
        refl
    ; separateCascadeConservationProved =
        false
    ; separateCascadeConservationProvedIsFalse =
        refl
    ; pillaiRouteSpeculative =
        true
    ; pillaiRouteSpeculativeIsTrue =
        refl
    ; unrestrictedClayNSRemainsFalse =
        true
    ; unrestrictedClayNSRemainsFalseIsTrue =
        refl
    ; nsClayPromoted =
        false
    ; nsClayPromotedIsFalse =
        refl
    ; nextInputNeeded =
        canonicalNSCarrierFrequencyNextInput
    ; nextInputNeededIsCanonical =
        refl
    ; statement =
        nsCarrierFrequencyProgrammeStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Adjacent-only arithmetic observation is recorded as interesting"
        ∷ "Option 1 is recorded as the most tractable next route"
        ∷ "The H74 route remains conditional because the Fourier restriction theorem is not supplied"
        ∷ "Exact prime-LP flow invariance and separate cascade conservation remain unproved"
        ∷ "The Pillai route is speculative and unrestricted Clay NS remains false"
        ∷ []
    }

nsCarrierFrequencyKeepsClayFalse :
  nsClayPromoted canonicalNSCarrierFrequencyProgrammeStatusReceipt ≡ false
nsCarrierFrequencyKeepsClayFalse =
  refl

nsCarrierFrequencyNextInputCanonical :
  nextInputNeeded canonicalNSCarrierFrequencyProgrammeStatusReceipt
    ≡ canonicalNSCarrierFrequencyNextInput
nsCarrierFrequencyNextInputCanonical =
  refl

nsCarrierFrequencyNoPromotion :
  NSCarrierFrequencyProgrammePromotion →
  ⊥
nsCarrierFrequencyNoPromotion =
  nsCarrierFrequencyProgrammePromotionImpossibleHere
