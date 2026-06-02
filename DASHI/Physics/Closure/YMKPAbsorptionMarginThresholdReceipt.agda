module DASHI.Physics.Closure.YMKPAbsorptionMarginThresholdReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.KPCouplingObstructionReceipt as KPC
import DASHI.Physics.Closure.YMBTPathCountingKPThresholdReceipt as Count

------------------------------------------------------------------------
-- YM KP strict absorption margin threshold.
--
-- This is the YM4 receipt in the Paper 3 roadmap.  It separates mere
-- convergence of the single-prime geometric KP tail from strict local
-- absorption, i.e. the local sum being below one.  In the p=7 bookkeeping
-- used by the current carrier receipts this records beta ~= 13.64 as the
-- live threshold, conditional on the real Wilson activity and cMin data.

data YMKPAbsorptionMarginStatus : Set where
  strictKPMarginThresholdRecorded :
    YMKPAbsorptionMarginStatus

data YMKPSeriesVerdict : Set where
  convergenceIsWeakerThanAbsorption :
    YMKPSeriesVerdict

data YMKPLocalSumMarginLaw : Set where
  localSumBelowOneRequiresLogTwoP :
    YMKPLocalSumMarginLaw

data YMKPAbsorptionMarginOpenObligation : Set where
  fixActualCarrierCMin :
    YMKPAbsorptionMarginOpenObligation

  defineActualWilsonActivity :
    YMKPAbsorptionMarginOpenObligation

  proveActualLocalKPSumBelowOne :
    YMKPAbsorptionMarginOpenObligation

canonicalYMKPAbsorptionMarginOpenObligations :
  List YMKPAbsorptionMarginOpenObligation
canonicalYMKPAbsorptionMarginOpenObligations =
  fixActualCarrierCMin
  ∷ defineActualWilsonActivity
  ∷ proveActualLocalKPSumBelowOne
  ∷ []

data YMKPAbsorptionMarginNonClaim : Set where
  noActualRhoLessThanOneClaim :
    YMKPAbsorptionMarginNonClaim

  noCarrierKPPassClaim :
    YMKPAbsorptionMarginNonClaim

  noBalabanRGClaim :
    YMKPAbsorptionMarginNonClaim

  noContinuumYangMillsClaim :
    YMKPAbsorptionMarginNonClaim

  noClayYangMillsPromotion :
    YMKPAbsorptionMarginNonClaim

canonicalYMKPAbsorptionMarginNonClaims :
  List YMKPAbsorptionMarginNonClaim
canonicalYMKPAbsorptionMarginNonClaims =
  noActualRhoLessThanOneClaim
  ∷ noCarrierKPPassClaim
  ∷ noBalabanRGClaim
  ∷ noContinuumYangMillsClaim
  ∷ noClayYangMillsPromotion
  ∷ []

data YMKPAbsorptionMarginPromotion : Set where

ymKPAbsorptionMarginPromotionImpossibleHere :
  YMKPAbsorptionMarginPromotion →
  ⊥
ymKPAbsorptionMarginPromotionImpossibleHere ()

p7AbsorptionBetaNumerator :
  Nat
p7AbsorptionBetaNumerator =
  1364

p7AbsorptionBetaDenominator :
  Nat
p7AbsorptionBetaDenominator =
  100

p7ConvergenceBetaNumerator :
  Nat
p7ConvergenceBetaNumerator =
  1013

p7ConvergenceBetaDenominator :
  Nat
p7ConvergenceBetaDenominator =
  100

absorptionThresholdSummary :
  String
absorptionThresholdSummary =
  "YM4: KP convergence at p=7 starts near beta 10.13, but strict local absorption needs beta*cMin-a > log(2p), recorded as beta approximately 13.64 before actual rho can be consumed."

record YMKPAbsorptionMarginThresholdReceipt : Setω where
  field
    status :
      YMKPAbsorptionMarginStatus

    statusIsCanonical :
      status ≡ strictKPMarginThresholdRecorded

    consumedCountingReceipt :
      Count.YMBTPathCountingKPThresholdReceipt

    countingReceiptOnlyConvergence :
      Count.strictAbsorptionMarginProved consumedCountingReceipt ≡ false

    consumedCouplingReceipt :
      KPC.KPCouplingObstructionReceipt

    couplingReceiptRecordsLogTwoP :
      KPC.kpMarginThresholdFormula consumedCouplingReceipt
      ≡
      KPC.kpMarginIncludesLogTwoP

    seriesVerdict :
      YMKPSeriesVerdict

    seriesVerdictIsStrict :
      seriesVerdict ≡ convergenceIsWeakerThanAbsorption

    marginLaw :
      YMKPLocalSumMarginLaw

    marginLawIsLogTwoP :
      marginLaw ≡ localSumBelowOneRequiresLogTwoP

    p7ConvergenceBetaNumeratorRecorded :
      Nat

    p7ConvergenceBetaNumeratorRecordedIsCanonical :
      p7ConvergenceBetaNumeratorRecorded ≡ p7ConvergenceBetaNumerator

    p7ConvergenceBetaDenominatorRecorded :
      Nat

    p7ConvergenceBetaDenominatorRecordedIsCanonical :
      p7ConvergenceBetaDenominatorRecorded ≡ p7ConvergenceBetaDenominator

    p7AbsorptionBetaNumeratorRecorded :
      Nat

    p7AbsorptionBetaNumeratorRecordedIsCanonical :
      p7AbsorptionBetaNumeratorRecorded ≡ p7AbsorptionBetaNumerator

    p7AbsorptionBetaDenominatorRecorded :
      Nat

    p7AbsorptionBetaDenominatorRecordedIsCanonical :
      p7AbsorptionBetaDenominatorRecorded ≡ p7AbsorptionBetaDenominator

    actualRhoMarginProved :
      Bool

    actualRhoMarginProvedIsFalse :
      actualRhoMarginProved ≡ false

    openObligations :
      List YMKPAbsorptionMarginOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalYMKPAbsorptionMarginOpenObligations

    nonClaims :
      List YMKPAbsorptionMarginNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalYMKPAbsorptionMarginNonClaims

    continuumYangMillsPromoted :
      Bool

    continuumYangMillsPromotedIsFalse :
      continuumYangMillsPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    summary :
      String

    summaryIsCanonical :
      summary ≡ absorptionThresholdSummary

open YMKPAbsorptionMarginThresholdReceipt public

canonicalYMKPAbsorptionMarginThresholdReceipt :
  YMKPAbsorptionMarginThresholdReceipt
canonicalYMKPAbsorptionMarginThresholdReceipt =
  record
    { status =
        strictKPMarginThresholdRecorded
    ; statusIsCanonical =
        refl
    ; consumedCountingReceipt =
        Count.canonicalYMBTPathCountingKPThresholdReceipt
    ; countingReceiptOnlyConvergence =
        refl
    ; consumedCouplingReceipt =
        KPC.canonicalKPCouplingObstructionReceipt
    ; couplingReceiptRecordsLogTwoP =
        refl
    ; seriesVerdict =
        convergenceIsWeakerThanAbsorption
    ; seriesVerdictIsStrict =
        refl
    ; marginLaw =
        localSumBelowOneRequiresLogTwoP
    ; marginLawIsLogTwoP =
        refl
    ; p7ConvergenceBetaNumeratorRecorded =
        p7ConvergenceBetaNumerator
    ; p7ConvergenceBetaNumeratorRecordedIsCanonical =
        refl
    ; p7ConvergenceBetaDenominatorRecorded =
        p7ConvergenceBetaDenominator
    ; p7ConvergenceBetaDenominatorRecordedIsCanonical =
        refl
    ; p7AbsorptionBetaNumeratorRecorded =
        p7AbsorptionBetaNumerator
    ; p7AbsorptionBetaNumeratorRecordedIsCanonical =
        refl
    ; p7AbsorptionBetaDenominatorRecorded =
        p7AbsorptionBetaDenominator
    ; p7AbsorptionBetaDenominatorRecordedIsCanonical =
        refl
    ; actualRhoMarginProved =
        false
    ; actualRhoMarginProvedIsFalse =
        refl
    ; openObligations =
        canonicalYMKPAbsorptionMarginOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; nonClaims =
        canonicalYMKPAbsorptionMarginNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; continuumYangMillsPromoted =
        false
    ; continuumYangMillsPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; summary =
        absorptionThresholdSummary
    ; summaryIsCanonical =
        refl
    }
