module DASHI.Physics.Closure.NSRegularityUpgradeReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- C1 Navier-Stokes regularity upgrade receipt.
--
-- This receipt records the new computation as a candidate upgrade only.
-- The programme is reopened beyond the earlier Leray-ceiling statement, but
-- the uniformity of the regularity estimate across carrier prime-LP
-- approximations remains open.  No Clay/global regularity promotion is made.

data NSRegularityUpgradeStatus : Set where
  nsRegularityProgrammeReopenedUniformityGap :
    NSRegularityUpgradeStatus

data NSRegularityUpgradeInput : Set where
  flowPreservationSummableForHsPositive :
    NSRegularityUpgradeInput

  adjacentOnlyDissipationDominanceHighFrequency :
    NSRegularityUpgradeInput

  carrierPrimeLPDensityInHs :
    NSRegularityUpgradeInput

canonicalNSRegularityUpgradeInputs :
  List NSRegularityUpgradeInput
canonicalNSRegularityUpgradeInputs =
  flowPreservationSummableForHsPositive
  ∷ adjacentOnlyDissipationDominanceHighFrequency
  ∷ carrierPrimeLPDensityInHs
  ∷ []

data NSRegularityUpgradeRemainingGap : Set where
  uniformityOfRegularityEstimate :
    NSRegularityUpgradeRemainingGap

canonicalNSRegularityUpgradeRemainingGaps :
  List NSRegularityUpgradeRemainingGap
canonicalNSRegularityUpgradeRemainingGaps =
  uniformityOfRegularityEstimate
  ∷ []

data NSRegularityUpgradePromotion : Set where

nsRegularityUpgradePromotionImpossibleHere :
  NSRegularityUpgradePromotion →
  ⊥
nsRegularityUpgradePromotionImpossibleHere ()

nsRegularityUpgradeStatement : String
nsRegularityUpgradeStatement =
  "C1 records that the NS programme is reopened: flow preservation is summable for Hs with s>0, adjacent-only dissipation dominance holds at high frequency for s>0, and carrier prime-LP projections are dense in Hs; the remaining gap is uniformity of the regularity estimate across approximations, so Clay/global regularity promotion remains false."

record NSRegularityUpgradeReceipt : Setω where
  field
    status :
      NSRegularityUpgradeStatus

    inputs :
      List NSRegularityUpgradeInput

    inputsAreCanonical :
      inputs ≡ canonicalNSRegularityUpgradeInputs

    flowPreservationBoundSummable :
      Bool

    flowPreservationBoundSummableIsTrue :
      flowPreservationBoundSummable ≡ true

    flowPreservationForHsPositive :
      Bool

    flowPreservationForHsPositiveIsTrue :
      flowPreservationForHsPositive ≡ true

    adjacentOnlyDissipationDominanceRecorded :
      Bool

    adjacentOnlyDissipationDominanceRecordedIsTrue :
      adjacentOnlyDissipationDominanceRecorded ≡ true

    dissipationDominatesHighFrequenciesForSPositive :
      Bool

    dissipationDominatesHighFrequenciesForSPositiveIsTrue :
      dissipationDominatesHighFrequenciesForSPositive ≡ true

    carrierStructuredDensityRecorded :
      Bool

    carrierStructuredDensityRecordedIsTrue :
      carrierStructuredDensityRecorded ≡ true

    carrierPrimeLPDenseInHs :
      Bool

    carrierPrimeLPDenseInHsIsTrue :
      carrierPrimeLPDenseInHs ≡ true

    nsRegularityProgrammeReopened :
      Bool

    nsRegularityProgrammeReopenedIsTrue :
      nsRegularityProgrammeReopened ≡ true

    nsLerayIsNotCeiling :
      Bool

    nsLerayIsNotCeilingIsTrue :
      nsLerayIsNotCeiling ≡ true

    candidateGlobalRegularityForHsPositive :
      Bool

    candidateGlobalRegularityForHsPositiveIsTrue :
      candidateGlobalRegularityForHsPositive ≡ true

    remainingGaps :
      List NSRegularityUpgradeRemainingGap

    remainingGapsAreCanonical :
      remainingGaps ≡ canonicalNSRegularityUpgradeRemainingGaps

    uniformityOfRegularityEstimateClosed :
      Bool

    uniformityOfRegularityEstimateClosedIsFalse :
      uniformityOfRegularityEstimateClosed ≡ false

    uniformityOfRegularityEstimateOpen :
      Bool

    uniformityOfRegularityEstimateOpenIsTrue :
      uniformityOfRegularityEstimateOpen ≡ true

    globalSmoothRegularityProved :
      Bool

    globalSmoothRegularityProvedIsFalse :
      globalSmoothRegularityProved ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsRegularityUpgradeStatement

    promotionFlags :
      List NSRegularityUpgradePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSRegularityUpgradeReceipt public

canonicalNSRegularityUpgradeReceipt :
  NSRegularityUpgradeReceipt
canonicalNSRegularityUpgradeReceipt =
  record
    { status =
        nsRegularityProgrammeReopenedUniformityGap
    ; inputs =
        canonicalNSRegularityUpgradeInputs
    ; inputsAreCanonical =
        refl
    ; flowPreservationBoundSummable =
        true
    ; flowPreservationBoundSummableIsTrue =
        refl
    ; flowPreservationForHsPositive =
        true
    ; flowPreservationForHsPositiveIsTrue =
        refl
    ; adjacentOnlyDissipationDominanceRecorded =
        true
    ; adjacentOnlyDissipationDominanceRecordedIsTrue =
        refl
    ; dissipationDominatesHighFrequenciesForSPositive =
        true
    ; dissipationDominatesHighFrequenciesForSPositiveIsTrue =
        refl
    ; carrierStructuredDensityRecorded =
        true
    ; carrierStructuredDensityRecordedIsTrue =
        refl
    ; carrierPrimeLPDenseInHs =
        true
    ; carrierPrimeLPDenseInHsIsTrue =
        refl
    ; nsRegularityProgrammeReopened =
        true
    ; nsRegularityProgrammeReopenedIsTrue =
        refl
    ; nsLerayIsNotCeiling =
        true
    ; nsLerayIsNotCeilingIsTrue =
        refl
    ; candidateGlobalRegularityForHsPositive =
        true
    ; candidateGlobalRegularityForHsPositiveIsTrue =
        refl
    ; remainingGaps =
        canonicalNSRegularityUpgradeRemainingGaps
    ; remainingGapsAreCanonical =
        refl
    ; uniformityOfRegularityEstimateClosed =
        false
    ; uniformityOfRegularityEstimateClosedIsFalse =
        refl
    ; uniformityOfRegularityEstimateOpen =
        true
    ; uniformityOfRegularityEstimateOpenIsTrue =
        refl
    ; globalSmoothRegularityProved =
        false
    ; globalSmoothRegularityProvedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; statement =
        nsRegularityUpgradeStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Flow preservation bound is recorded as summable for Hs data with s>0"
        ∷ "Adjacent-only dissipation dominance is recorded at high frequency for s>0"
        ∷ "Carrier prime-LP projections are recorded as dense in Hs"
        ∷ "The NS programme is reopened beyond the previous Leray-ceiling summary"
        ∷ "The remaining gap is uniformity of the regularity estimate across approximations"
        ∷ "Global smooth regularity and Clay Navier-Stokes promotion remain false"
        ∷ []
    }

nsRegularityUpgradeKeepsUniformityOpen :
  uniformityOfRegularityEstimateOpen canonicalNSRegularityUpgradeReceipt
  ≡
  true
nsRegularityUpgradeKeepsUniformityOpen =
  refl

nsRegularityUpgradeKeepsClayFalse :
  clayNavierStokesPromoted canonicalNSRegularityUpgradeReceipt
  ≡
  false
nsRegularityUpgradeKeepsClayFalse =
  refl

nsRegularityUpgradeNoPromotion :
  NSRegularityUpgradePromotion →
  ⊥
nsRegularityUpgradeNoPromotion =
  nsRegularityUpgradePromotionImpossibleHere
