module DASHI.Physics.Closure.YMActualKPLocalSumDiameter1Receipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_<_)
open import Data.Nat.Properties as NatP using (m≤m+n)

import DASHI.Physics.Closure.YMActualP7WilsonPolymerActivityReceipt as Activity

------------------------------------------------------------------------
-- YM actual KP local-sum receipt, diameter 1.
--
-- This is a finite carrier/combinatorial receipt only.  It consumes the
-- actual p=7 Wilson polymer activity definition and records a diameter-1
-- local KP envelope with seven non-backtracking branches.  The envelope is
-- deliberately rational and concrete:
--
--   localSum(diameter <= 1) <= 7 / 28 < 1.
--
-- The global KP local-sum theorem, all higher-diameter tails, the physical
-- bridge, continuum Yang-Mills, and Clay promotion remain fail-closed.

data YMActualKPLocalSumDiameter1Status : Set where
  actualKPLocalSumDiameter1FiniteBoundRecorded :
    YMActualKPLocalSumDiameter1Status

data Diameter1BoundKind : Set where
  p7SingleStepNonBacktrackingEnvelope :
    Diameter1BoundKind

data Diameter1SuppressionLaw : Set where
  contourActionSuppression :
    Diameter1SuppressionLaw

data Diameter1OpenFlag : Set where
  higherDiameterTailOpen :
    Diameter1OpenFlag

  physicalBetaBridgeOpen :
    Diameter1OpenFlag

  globalKPLocalSumOpen :
    Diameter1OpenFlag

canonicalDiameter1OpenFlags :
  List Diameter1OpenFlag
canonicalDiameter1OpenFlags =
  higherDiameterTailOpen
  ∷ physicalBetaBridgeOpen
  ∷ globalKPLocalSumOpen
  ∷ []

data Diameter1NonClaim : Set where
  noHigherDiameterTailBound :
    Diameter1NonClaim

  noGlobalKPPassClaim :
    Diameter1NonClaim

  noPhysicalYangMillsPromotion :
    Diameter1NonClaim

  noClayYangMillsPromotion :
    Diameter1NonClaim

canonicalDiameter1NonClaims :
  List Diameter1NonClaim
canonicalDiameter1NonClaims =
  noHigherDiameterTailBound
  ∷ noGlobalKPPassClaim
  ∷ noPhysicalYangMillsPromotion
  ∷ noClayYangMillsPromotion
  ∷ []

data YMActualKPLocalSumDiameter1Promotion : Set where

ymActualKPLocalSumDiameter1PromotionImpossibleHere :
  YMActualKPLocalSumDiameter1Promotion →
  ⊥
ymActualKPLocalSumDiameter1PromotionImpossibleHere ()

p7Diameter1BranchCount :
  Nat
p7Diameter1BranchCount =
  7

diameter1ActivityWeightDenominator :
  Nat
diameter1ActivityWeightDenominator =
  28

diameter1LocalSumNumerator :
  Nat
diameter1LocalSumNumerator =
  p7Diameter1BranchCount

diameter1LocalSumDenominator :
  Nat
diameter1LocalSumDenominator =
  diameter1ActivityWeightDenominator

diameter1LocalSumBelowOne :
  diameter1LocalSumNumerator < diameter1LocalSumDenominator
diameter1LocalSumBelowOne =
  NatP.m≤m+n 8 20

diameter1BoundReading :
  String
diameter1BoundReading =
  "Diameter-1 actual p=7 KP local-sum envelope: seven retained same-prime non-backtracking branches, using contour/action suppression |z Gamma| <= C0^|Gamma| exp(-beta*c_min*|Gamma|), give the finite diameter-1 bound."

diameter1FailClosedReading :
  String
diameter1FailClosedReading =
  "This receipt closes only the diameter-1 finite envelope; higher-diameter tails, physical beta interpretation, global KP pass, continuum Yang-Mills, and Clay promotion remain false."

diameter1SuppressionReading :
  String
diameter1SuppressionReading =
  "The large-beta estimate is not |exp(-beta S)-1| <= beta*S as a suppression mechanism; suppression is the contour/activity bound C0^|Gamma| exp(-beta*c_min*|Gamma|)."

record Diameter1LocalSumEnvelope : Set where
  field
    branchCount :
      Nat

    branchCountIsP7 :
      branchCount ≡ p7Diameter1BranchCount

    activityWeightDenominator :
      Nat

    activityWeightDenominatorIsCanonical :
      activityWeightDenominator ≡ diameter1ActivityWeightDenominator

    localSumNumerator :
      Nat

    localSumNumeratorIsCanonical :
      localSumNumerator ≡ diameter1LocalSumNumerator

    localSumDenominator :
      Nat

    localSumDenominatorIsCanonical :
      localSumDenominator ≡ diameter1LocalSumDenominator

    localSumBelowOne :
      localSumNumerator < localSumDenominator

open Diameter1LocalSumEnvelope public

canonicalDiameter1LocalSumEnvelope :
  Diameter1LocalSumEnvelope
canonicalDiameter1LocalSumEnvelope =
  record
    { branchCount =
        p7Diameter1BranchCount
    ; branchCountIsP7 =
        refl
    ; activityWeightDenominator =
        diameter1ActivityWeightDenominator
    ; activityWeightDenominatorIsCanonical =
        refl
    ; localSumNumerator =
        diameter1LocalSumNumerator
    ; localSumNumeratorIsCanonical =
        refl
    ; localSumDenominator =
        diameter1LocalSumDenominator
    ; localSumDenominatorIsCanonical =
        refl
    ; localSumBelowOne =
        diameter1LocalSumBelowOne
    }

record YMActualKPLocalSumDiameter1Receipt : Setω where
  field
    status :
      YMActualKPLocalSumDiameter1Status

    statusIsCanonical :
      status ≡ actualKPLocalSumDiameter1FiniteBoundRecorded

    actualActivityReceipt :
      Activity.YMActualP7WilsonPolymerActivityReceipt

    actualActivityDefined :
      Activity.actualPolymerActivityDefined actualActivityReceipt ≡ true

    sourceNowRecordsGlobalLocalSum :
      Activity.localKPSumBelowOneProved actualActivityReceipt ≡ true

    boundKind :
      Diameter1BoundKind

    boundKindIsP7SingleStep :
      boundKind ≡ p7SingleStepNonBacktrackingEnvelope

    suppressionLaw :
      Diameter1SuppressionLaw

    suppressionLawIsContourAction :
      suppressionLaw ≡ contourActionSuppression

    zBoundUsesContourActionSuppression :
      Bool

    zBoundUsesContourActionSuppressionIsTrue :
      zBoundUsesContourActionSuppression ≡ true

    betaSLargeBetaSuppressionUsed :
      Bool

    betaSLargeBetaSuppressionUsedIsFalse :
      betaSLargeBetaSuppressionUsed ≡ false

    envelope :
      Diameter1LocalSumEnvelope

    envelopeIsCanonical :
      envelope ≡ canonicalDiameter1LocalSumEnvelope

    finiteDiameterLocalSumBelowOne :
      localSumNumerator envelope < localSumDenominator envelope

    finiteDiameterLocalSumClosed :
      Bool

    finiteDiameterLocalSumClosedIsTrue :
      finiteDiameterLocalSumClosed ≡ true

    higherDiameterClosed :
      Bool

    higherDiameterClosedIsFalse :
      higherDiameterClosed ≡ false

    physicalBridgeClosed :
      Bool

    physicalBridgeClosedIsFalse :
      physicalBridgeClosed ≡ false

    globalKPLocalSumClosed :
      Bool

    globalKPLocalSumClosedIsFalse :
      globalKPLocalSumClosed ≡ false

    continuumYangMillsPromoted :
      Bool

    continuumYangMillsPromotedIsFalse :
      continuumYangMillsPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    openFlags :
      List Diameter1OpenFlag

    openFlagsAreCanonical :
      openFlags ≡ canonicalDiameter1OpenFlags

    nonClaims :
      List Diameter1NonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalDiameter1NonClaims

    noPromotion :
      YMActualKPLocalSumDiameter1Promotion →
      ⊥

    boundSummary :
      String

    boundSummaryIsCanonical :
      boundSummary ≡ diameter1BoundReading

    failClosedSummary :
      String

    failClosedSummaryIsCanonical :
      failClosedSummary ≡ diameter1FailClosedReading

    suppressionSummary :
      String

    suppressionSummaryIsCanonical :
      suppressionSummary ≡ diameter1SuppressionReading

open YMActualKPLocalSumDiameter1Receipt public

canonicalYMActualKPLocalSumDiameter1Receipt :
  YMActualKPLocalSumDiameter1Receipt
canonicalYMActualKPLocalSumDiameter1Receipt =
  record
    { status =
        actualKPLocalSumDiameter1FiniteBoundRecorded
    ; statusIsCanonical =
        refl
    ; actualActivityReceipt =
        Activity.canonicalYMActualP7WilsonPolymerActivityReceipt
    ; actualActivityDefined =
        refl
    ; sourceNowRecordsGlobalLocalSum =
        refl
    ; boundKind =
        p7SingleStepNonBacktrackingEnvelope
    ; boundKindIsP7SingleStep =
        refl
    ; suppressionLaw =
        contourActionSuppression
    ; suppressionLawIsContourAction =
        refl
    ; zBoundUsesContourActionSuppression =
        true
    ; zBoundUsesContourActionSuppressionIsTrue =
        refl
    ; betaSLargeBetaSuppressionUsed =
        false
    ; betaSLargeBetaSuppressionUsedIsFalse =
        refl
    ; envelope =
        canonicalDiameter1LocalSumEnvelope
    ; envelopeIsCanonical =
        refl
    ; finiteDiameterLocalSumBelowOne =
        diameter1LocalSumBelowOne
    ; finiteDiameterLocalSumClosed =
        true
    ; finiteDiameterLocalSumClosedIsTrue =
        refl
    ; higherDiameterClosed =
        false
    ; higherDiameterClosedIsFalse =
        refl
    ; physicalBridgeClosed =
        false
    ; physicalBridgeClosedIsFalse =
        refl
    ; globalKPLocalSumClosed =
        false
    ; globalKPLocalSumClosedIsFalse =
        refl
    ; continuumYangMillsPromoted =
        false
    ; continuumYangMillsPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; openFlags =
        canonicalDiameter1OpenFlags
    ; openFlagsAreCanonical =
        refl
    ; nonClaims =
        canonicalDiameter1NonClaims
    ; nonClaimsAreCanonical =
        refl
    ; noPromotion =
        ymActualKPLocalSumDiameter1PromotionImpossibleHere
    ; boundSummary =
        diameter1BoundReading
    ; boundSummaryIsCanonical =
        refl
    ; failClosedSummary =
        diameter1FailClosedReading
    ; failClosedSummaryIsCanonical =
        refl
    ; suppressionSummary =
        diameter1SuppressionReading
    ; suppressionSummaryIsCanonical =
        refl
    }

canonicalDiameter1FiniteLocalSumClosed :
  finiteDiameterLocalSumClosed canonicalYMActualKPLocalSumDiameter1Receipt
  ≡
  true
canonicalDiameter1FiniteLocalSumClosed =
  refl

canonicalDiameter1GlobalKPStillOpen :
  globalKPLocalSumClosed canonicalYMActualKPLocalSumDiameter1Receipt
  ≡
  false
canonicalDiameter1GlobalKPStillOpen =
  refl
