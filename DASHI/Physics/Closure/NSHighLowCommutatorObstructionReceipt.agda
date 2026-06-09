module DASHI.Physics.Closure.NSHighLowCommutatorObstructionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSHighLowFluxControlAuditReceipt
  as Audit

------------------------------------------------------------------------
-- NS HighLow commutator obstruction.
--
-- This receipt records the proved energy-transport cancellation, the exact
-- HighLow commutator reduction, and the live low-mode Lipschitz obstruction.

data NSHighLowCommutatorObstructionStatus : Set where
  nsHighLowCommutatorObstructionRecorded_noPromotion :
    NSHighLowCommutatorObstructionStatus

data NSHighLowCommutatorFact : Set where
  transportTermVanishesExactly :
    NSHighLowCommutatorFact

  highLowEqualsCommutator :
    NSHighLowCommutatorFact

  kMinusHalfClaimRetracted :
    NSHighLowCommutatorFact

  lerayBernsteinGrowsInK :
    NSHighLowCommutatorFact

  liveObstructionIsCommutatorLipschitzControl :
    NSHighLowCommutatorFact

canonicalNSHighLowCommutatorFacts :
  List NSHighLowCommutatorFact
canonicalNSHighLowCommutatorFacts =
  transportTermVanishesExactly
  ∷ highLowEqualsCommutator
  ∷ kMinusHalfClaimRetracted
  ∷ lerayBernsteinGrowsInK
  ∷ liveObstructionIsCommutatorLipschitzControl
  ∷ []

data HighLowOutcome : Set where
  highLowControlled :
    HighLowOutcome

  highLowCounterfamily :
    HighLowOutcome

canonicalHighLowOutcomes :
  List HighLowOutcome
canonicalHighLowOutcomes =
  highLowControlled
  ∷ highLowCounterfamily
  ∷ []

data NSHighLowCommutatorObstructionPromotion : Set where

nsHighLowCommutatorObstructionPromotionImpossibleHere :
  NSHighLowCommutatorObstructionPromotion →
  ⊥
nsHighLowCommutatorObstructionPromotionImpossibleHere ()

transportCancellationText : String
transportCancellationText =
  "<(u_<K . grad)u_>K,u_>K>=0 by integration by parts and div u_<K=0."

commutatorReductionText : String
commutatorReductionText =
  "B_HL = <[P_>K,u_<K.grad]u_>K,u_>K> after the transport term cancels."

correctBernsteinGrowthText : String
correctBernsteinGrowthText =
  "Leray plus Bernstein gives growing low-mode Lipschitz control, not K^{-1/2} suppression."

liveObstructionText : String
liveObstructionText =
  "CommutatorLipschitzControlWithoutRegularity: control the low-mode Lipschitz factor without Serrin, BKM, global H118, or hidden L_infinity."

commutatorBoundaryText : String
commutatorBoundaryText =
  "This receipt records cancellation and obstruction facts only. It does not prove CommutatorLipschitzControl, CumulativeTailDissipationDominance, K* no-drift, H118 regularity, or Clay NS."

record NSHighLowCommutatorObstructionReceipt : Setω where
  field
    status :
      NSHighLowCommutatorObstructionStatus

    statusIsCanonical :
      status ≡ nsHighLowCommutatorObstructionRecorded_noPromotion

    auditReceipt :
      Audit.NSHighLowFluxControlAuditReceipt

    auditTransportCancellationRecorded :
      Audit.transportTermVanishesExactly auditReceipt ≡ true

    auditCommutatorOnlyRecorded :
      Audit.highLowEqualsCommutatorOnly auditReceipt ≡ true

    auditKMinusHalfRetracted :
      Audit.kMinusHalfClaimRetracted auditReceipt ≡ true

    auditHighLowStillRejected :
      Audit.highLowBoundAccepted auditReceipt ≡ false

    facts :
      List NSHighLowCommutatorFact

    factsAreCanonical :
      facts ≡ canonicalNSHighLowCommutatorFacts

    possibleOutcomes :
      List HighLowOutcome

    possibleOutcomesAreCanonical :
      possibleOutcomes ≡ canonicalHighLowOutcomes

    transportTermVanishes :
      Bool

    transportTermVanishesIsTrue :
      transportTermVanishes ≡ true

    highLowEqualsCommutatorRecorded :
      Bool

    highLowEqualsCommutatorRecordedIsTrue :
      highLowEqualsCommutatorRecorded ≡ true

    kMinusHalfClaimRetractedRecorded :
      Bool

    kMinusHalfClaimRetractedRecordedIsTrue :
      kMinusHalfClaimRetractedRecorded ≡ true

    correctBernsteinGrowth :
      String

    correctBernsteinGrowthIsCanonical :
      correctBernsteinGrowth ≡ correctBernsteinGrowthText

    liveObstruction :
      Set

    highLowBoundAccepted :
      Bool

    highLowBoundAcceptedIsFalse :
      highLowBoundAccepted ≡ false

    commutatorLipschitzControlProved :
      Bool

    commutatorLipschitzControlProvedIsFalse :
      commutatorLipschitzControlProved ≡ false

    cumulativeTailDissipationDominanceProved :
      Bool

    cumulativeTailDissipationDominanceProvedIsFalse :
      cumulativeTailDissipationDominanceProved ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    promotions :
      List NSHighLowCommutatorObstructionPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      NSHighLowCommutatorObstructionPromotion →
      ⊥

    transportCancellation :
      String

    transportCancellationIsCanonical :
      transportCancellation ≡ transportCancellationText

    commutatorReduction :
      String

    commutatorReductionIsCanonical :
      commutatorReduction ≡ commutatorReductionText

    liveObstructionDescription :
      String

    liveObstructionDescriptionIsCanonical :
      liveObstructionDescription ≡ liveObstructionText

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ commutatorBoundaryText

open NSHighLowCommutatorObstructionReceipt public

canonicalNSHighLowCommutatorObstructionReceipt :
  NSHighLowCommutatorObstructionReceipt
canonicalNSHighLowCommutatorObstructionReceipt =
  record
    { status =
        nsHighLowCommutatorObstructionRecorded_noPromotion
    ; statusIsCanonical =
        refl
    ; auditReceipt =
        Audit.canonicalNSHighLowFluxControlAuditReceipt
    ; auditTransportCancellationRecorded =
        refl
    ; auditCommutatorOnlyRecorded =
        refl
    ; auditKMinusHalfRetracted =
        refl
    ; auditHighLowStillRejected =
        refl
    ; facts =
        canonicalNSHighLowCommutatorFacts
    ; factsAreCanonical =
        refl
    ; possibleOutcomes =
        canonicalHighLowOutcomes
    ; possibleOutcomesAreCanonical =
        refl
    ; transportTermVanishes =
        true
    ; transportTermVanishesIsTrue =
        refl
    ; highLowEqualsCommutatorRecorded =
        true
    ; highLowEqualsCommutatorRecordedIsTrue =
        refl
    ; kMinusHalfClaimRetractedRecorded =
        true
    ; kMinusHalfClaimRetractedRecordedIsTrue =
        refl
    ; correctBernsteinGrowth =
        correctBernsteinGrowthText
    ; correctBernsteinGrowthIsCanonical =
        refl
    ; liveObstruction =
        ⊥
    ; highLowBoundAccepted =
        false
    ; highLowBoundAcceptedIsFalse =
        refl
    ; commutatorLipschitzControlProved =
        false
    ; commutatorLipschitzControlProvedIsFalse =
        refl
    ; cumulativeTailDissipationDominanceProved =
        false
    ; cumulativeTailDissipationDominanceProvedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        nsHighLowCommutatorObstructionPromotionImpossibleHere
    ; transportCancellation =
        transportCancellationText
    ; transportCancellationIsCanonical =
        refl
    ; commutatorReduction =
        commutatorReductionText
    ; commutatorReductionIsCanonical =
        refl
    ; liveObstructionDescription =
        liveObstructionText
    ; liveObstructionDescriptionIsCanonical =
        refl
    ; boundary =
        commutatorBoundaryText
    ; boundaryIsCanonical =
        refl
    }

canonicalCommutatorObstructionKeepsNSFalse :
  clayNavierStokesPromoted canonicalNSHighLowCommutatorObstructionReceipt
  ≡
  false
canonicalCommutatorObstructionKeepsNSFalse =
  refl
