module DASHI.Physics.Closure.YMBTPathCountingKPThresholdReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.BruhatTitsBraidKPReductionReceipt as BT

------------------------------------------------------------------------
-- YM Bruhat-Tits path counting and KP convergence threshold.
--
-- This is the YM2/YM3 receipt in the Paper 3 roadmap.  It records the
-- combinatorial counting shape: a p-lane Bruhat-Tits tree is (p+1)-regular,
-- and non-backtracking paths through a fixed edge carry p^n branching.
-- Therefore the local geometric KP tail converges only under the
-- beta*cMin(p)-a > log p threshold.  Strict absorption is not claimed here;
-- it is a separate log(2p) receipt.

data YMBTPathCountingStatus : Set where
  btPathCountingKPThresholdRecorded :
    YMBTPathCountingStatus

data YMBTPathCountingLaw : Set where
  lengthNPathsBoundedByPToN :
    YMBTPathCountingLaw

data YMKPConvergenceThresholdLaw : Set where
  convergenceRequiresBetaCMinMinusAGreaterThanLogP :
    YMKPConvergenceThresholdLaw

data YMBTCountingNonClaim : Set where
  noStrictKPMarginClaim :
    YMBTCountingNonClaim

  noActualPolymerActivityClaim :
    YMBTCountingNonClaim

  noBalabanRGClaim :
    YMBTCountingNonClaim

  noContinuumYangMillsClaim :
    YMBTCountingNonClaim

  noClayYangMillsPromotion :
    YMBTCountingNonClaim

canonicalYMBTCountingNonClaims :
  List YMBTCountingNonClaim
canonicalYMBTCountingNonClaims =
  noStrictKPMarginClaim
  ∷ noActualPolymerActivityClaim
  ∷ noBalabanRGClaim
  ∷ noContinuumYangMillsClaim
  ∷ noClayYangMillsPromotion
  ∷ []

data YMBTCountingPromotion : Set where

ymBTCountingPromotionImpossibleHere :
  YMBTCountingPromotion →
  ⊥
ymBTCountingPromotionImpossibleHere ()

p7Prime :
  Nat
p7Prime =
  7

p7BTValency :
  Nat
p7BTValency =
  8

p7NonBacktrackingBranching :
  Nat
p7NonBacktrackingBranching =
  7

p7ConvergenceBetaNumerator :
  Nat
p7ConvergenceBetaNumerator =
  1013

p7ConvergenceBetaDenominator :
  Nat
p7ConvergenceBetaDenominator =
  100

pathCountingSummary :
  String
pathCountingSummary =
  "YM2/YM3: p-lane BT tree path counting gives p^n local branching; for p=7 the convergence threshold is beta approximately 10.13, not a KP absorption pass."

record YMBTPathCountingKPThresholdReceipt : Setω where
  field
    status :
      YMBTPathCountingStatus

    statusIsCanonical :
      status ≡ btPathCountingKPThresholdRecorded

    consumedBTReceipt :
      BT.BruhatTitsBraidKPReductionReceipt

    consumedBTRecordsP7Valency :
      BT.p7ValencyRecorded consumedBTReceipt ≡ BT.p7BTValency

    consumedBTRecordsBranching :
      BT.p7BranchingFactorRecorded consumedBTReceipt
      ≡
      BT.p7BranchingFactor

    pathCountingLaw :
      YMBTPathCountingLaw

    pathCountingLawIsPToN :
      pathCountingLaw ≡ lengthNPathsBoundedByPToN

    convergenceThresholdLaw :
      YMKPConvergenceThresholdLaw

    convergenceThresholdLawIsLogP :
      convergenceThresholdLaw
      ≡
      convergenceRequiresBetaCMinMinusAGreaterThanLogP

    p7PrimeRecorded :
      Nat

    p7PrimeRecordedIsCanonical :
      p7PrimeRecorded ≡ p7Prime

    p7ValencyRecorded :
      Nat

    p7ValencyRecordedIsCanonical :
      p7ValencyRecorded ≡ p7BTValency

    p7BranchingRecorded :
      Nat

    p7BranchingRecordedIsCanonical :
      p7BranchingRecorded ≡ p7NonBacktrackingBranching

    p7ConvergenceBetaNumeratorRecorded :
      Nat

    p7ConvergenceBetaNumeratorRecordedIsCanonical :
      p7ConvergenceBetaNumeratorRecorded ≡ p7ConvergenceBetaNumerator

    p7ConvergenceBetaDenominatorRecorded :
      Nat

    p7ConvergenceBetaDenominatorRecordedIsCanonical :
      p7ConvergenceBetaDenominatorRecorded ≡ p7ConvergenceBetaDenominator

    strictAbsorptionMarginProved :
      Bool

    strictAbsorptionMarginProvedIsFalse :
      strictAbsorptionMarginProved ≡ false

    actualPolymerActivityDefined :
      Bool

    actualPolymerActivityDefinedIsFalseHere :
      actualPolymerActivityDefined ≡ false

    nonClaims :
      List YMBTCountingNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalYMBTCountingNonClaims

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
      summary ≡ pathCountingSummary

open YMBTPathCountingKPThresholdReceipt public

canonicalYMBTPathCountingKPThresholdReceipt :
  YMBTPathCountingKPThresholdReceipt
canonicalYMBTPathCountingKPThresholdReceipt =
  record
    { status =
        btPathCountingKPThresholdRecorded
    ; statusIsCanonical =
        refl
    ; consumedBTReceipt =
        BT.canonicalBruhatTitsBraidKPReductionReceipt
    ; consumedBTRecordsP7Valency =
        refl
    ; consumedBTRecordsBranching =
        refl
    ; pathCountingLaw =
        lengthNPathsBoundedByPToN
    ; pathCountingLawIsPToN =
        refl
    ; convergenceThresholdLaw =
        convergenceRequiresBetaCMinMinusAGreaterThanLogP
    ; convergenceThresholdLawIsLogP =
        refl
    ; p7PrimeRecorded =
        p7Prime
    ; p7PrimeRecordedIsCanonical =
        refl
    ; p7ValencyRecorded =
        p7BTValency
    ; p7ValencyRecordedIsCanonical =
        refl
    ; p7BranchingRecorded =
        p7NonBacktrackingBranching
    ; p7BranchingRecordedIsCanonical =
        refl
    ; p7ConvergenceBetaNumeratorRecorded =
        p7ConvergenceBetaNumerator
    ; p7ConvergenceBetaNumeratorRecordedIsCanonical =
        refl
    ; p7ConvergenceBetaDenominatorRecorded =
        p7ConvergenceBetaDenominator
    ; p7ConvergenceBetaDenominatorRecordedIsCanonical =
        refl
    ; strictAbsorptionMarginProved =
        false
    ; strictAbsorptionMarginProvedIsFalse =
        refl
    ; actualPolymerActivityDefined =
        false
    ; actualPolymerActivityDefinedIsFalseHere =
        refl
    ; nonClaims =
        canonicalYMBTCountingNonClaims
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
        pathCountingSummary
    ; summaryIsCanonical =
        refl
    }
