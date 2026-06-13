module DASHI.Physics.Closure.YMActualKPLocalSumDiameter2Receipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_<_)
open import Data.Nat.Properties as NatP using (m≤m+n)

import DASHI.Physics.Closure.YMActualKPLocalSumDiameter1Receipt as D1
import DASHI.Physics.Closure.YMActualP7WilsonPolymerActivityReceipt as Activity

------------------------------------------------------------------------
-- YM actual KP local-sum receipt, diameter 2.
--
-- This is a finite carrier/combinatorial receipt only.  It extends the
-- diameter-1 envelope by adding the second p=7 non-backtracking shell:
--
--   shell_1 = 7, shell_2 = 49,
--   localSum(diameter <= 2) <= (7 + 49) / 112 = 56 / 112 < 1.
--
-- The bound is a concrete finite receipt, not a global KP theorem.  The
-- diameter >= 3 tail, physical bridge, continuum Yang-Mills construction,
-- mass gap, and Clay promotion remain fail-closed.

data YMActualKPLocalSumDiameter2Status : Set where
  actualKPLocalSumDiameter2FiniteBoundRecorded :
    YMActualKPLocalSumDiameter2Status

data Diameter2BoundKind : Set where
  p7TwoStepNonBacktrackingEnvelope :
    Diameter2BoundKind

data Diameter2SuppressionLaw : Set where
  contourActionSuppression :
    Diameter2SuppressionLaw

data Diameter2OpenFlag : Set where
  diameterAtLeastThreeTailOpen :
    Diameter2OpenFlag

  physicalBetaBridgeOpen :
    Diameter2OpenFlag

  globalKPLocalSumOpen :
    Diameter2OpenFlag

  balabanRGTransferOpen :
    Diameter2OpenFlag

canonicalDiameter2OpenFlags :
  List Diameter2OpenFlag
canonicalDiameter2OpenFlags =
  diameterAtLeastThreeTailOpen
  ∷ physicalBetaBridgeOpen
  ∷ globalKPLocalSumOpen
  ∷ balabanRGTransferOpen
  ∷ []

data Diameter2NonClaim : Set where
  noDiameterAtLeastThreeTailBound :
    Diameter2NonClaim

  noGlobalKPPassClaim :
    Diameter2NonClaim

  noBalabanRGTransferClaim :
    Diameter2NonClaim

  noPhysicalYangMillsPromotion :
    Diameter2NonClaim

  noMassGapClaim :
    Diameter2NonClaim

  noClayYangMillsPromotion :
    Diameter2NonClaim

canonicalDiameter2NonClaims :
  List Diameter2NonClaim
canonicalDiameter2NonClaims =
  noDiameterAtLeastThreeTailBound
  ∷ noGlobalKPPassClaim
  ∷ noBalabanRGTransferClaim
  ∷ noPhysicalYangMillsPromotion
  ∷ noMassGapClaim
  ∷ noClayYangMillsPromotion
  ∷ []

data YMActualKPLocalSumDiameter2Promotion : Set where

ymActualKPLocalSumDiameter2PromotionImpossibleHere :
  YMActualKPLocalSumDiameter2Promotion →
  ⊥
ymActualKPLocalSumDiameter2PromotionImpossibleHere ()

p7Diameter2Shell1Count :
  Nat
p7Diameter2Shell1Count =
  7

p7Diameter2Shell2Count :
  Nat
p7Diameter2Shell2Count =
  49

diameter2ActivityWeightDenominator :
  Nat
diameter2ActivityWeightDenominator =
  112

diameter2LocalSumNumerator :
  Nat
diameter2LocalSumNumerator =
  p7Diameter2Shell1Count + p7Diameter2Shell2Count

diameter2LocalSumDenominator :
  Nat
diameter2LocalSumDenominator =
  diameter2ActivityWeightDenominator

diameter2LocalSumBelowOne :
  diameter2LocalSumNumerator < diameter2LocalSumDenominator
diameter2LocalSumBelowOne =
  NatP.m≤m+n 57 55

diameter2BoundReading :
  String
diameter2BoundReading =
  "Diameter-2 actual p=7 KP local-sum envelope: shell counts 7 and 49 are consumed through contour/action suppression |z Gamma| <= C0^|Gamma| exp(-beta*c_min*|Gamma|), giving the finite diameter-2 bound."

diameter2FailClosedReading :
  String
diameter2FailClosedReading =
  "This receipt closes only the diameter-2 finite envelope; diameter >= 3 tails, physical beta interpretation, Balaban transfer, global KP pass, continuum Yang-Mills, mass gap, and Clay promotion remain false."

diameter2SuppressionReading :
  String
diameter2SuppressionReading =
  "The diameter-2 receipt rejects the large-beta suppression reading |exp(-beta S)-1| <= beta*S; the recorded KP activity suppression is contour/action exponential decay in |Gamma|."

record Diameter2LocalSumEnvelope : Set where
  field
    shell1Count :
      Nat

    shell1CountIsP7 :
      shell1Count ≡ p7Diameter2Shell1Count

    shell2Count :
      Nat

    shell2CountIsP7Squared :
      shell2Count ≡ p7Diameter2Shell2Count

    localSumNumerator :
      Nat

    localSumNumeratorIsCanonical :
      localSumNumerator ≡ diameter2LocalSumNumerator

    localSumDenominator :
      Nat

    localSumDenominatorIsCanonical :
      localSumDenominator ≡ diameter2LocalSumDenominator

    localSumBelowOne :
      localSumNumerator < localSumDenominator

open Diameter2LocalSumEnvelope public

canonicalDiameter2LocalSumEnvelope :
  Diameter2LocalSumEnvelope
canonicalDiameter2LocalSumEnvelope =
  record
    { shell1Count =
        p7Diameter2Shell1Count
    ; shell1CountIsP7 =
        refl
    ; shell2Count =
        p7Diameter2Shell2Count
    ; shell2CountIsP7Squared =
        refl
    ; localSumNumerator =
        diameter2LocalSumNumerator
    ; localSumNumeratorIsCanonical =
        refl
    ; localSumDenominator =
        diameter2LocalSumDenominator
    ; localSumDenominatorIsCanonical =
        refl
    ; localSumBelowOne =
        diameter2LocalSumBelowOne
    }

record YMActualKPLocalSumDiameter2Receipt : Setω where
  field
    status :
      YMActualKPLocalSumDiameter2Status

    statusIsCanonical :
      status ≡ actualKPLocalSumDiameter2FiniteBoundRecorded

    actualActivityReceipt :
      Activity.YMActualP7WilsonPolymerActivityReceipt

    actualActivityDefined :
      Activity.actualPolymerActivityDefined actualActivityReceipt ≡ true

    sourceNowRecordsGlobalLocalSum :
      Activity.localKPSumBelowOneProved actualActivityReceipt ≡ true

    diameter1Receipt :
      D1.YMActualKPLocalSumDiameter1Receipt

    diameter1FiniteBoundClosed :
      D1.finiteDiameterLocalSumClosed diameter1Receipt ≡ true

    diameter1GlobalKPStillOpen :
      D1.globalKPLocalSumClosed diameter1Receipt ≡ false

    boundKind :
      Diameter2BoundKind

    boundKindIsP7TwoStep :
      boundKind ≡ p7TwoStepNonBacktrackingEnvelope

    suppressionLaw :
      Diameter2SuppressionLaw

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
      Diameter2LocalSumEnvelope

    envelopeIsCanonical :
      envelope ≡ canonicalDiameter2LocalSumEnvelope

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

    balabanRGTransferClosed :
      Bool

    balabanRGTransferClosedIsFalse :
      balabanRGTransferClosed ≡ false

    globalKPLocalSumClosed :
      Bool

    globalKPLocalSumClosedIsFalse :
      globalKPLocalSumClosed ≡ false

    continuumYangMillsPromoted :
      Bool

    continuumYangMillsPromotedIsFalse :
      continuumYangMillsPromoted ≡ false

    massGapPromoted :
      Bool

    massGapPromotedIsFalse :
      massGapPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    openFlags :
      List Diameter2OpenFlag

    openFlagsAreCanonical :
      openFlags ≡ canonicalDiameter2OpenFlags

    nonClaims :
      List Diameter2NonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalDiameter2NonClaims

    noPromotion :
      YMActualKPLocalSumDiameter2Promotion →
      ⊥

    boundSummary :
      String

    boundSummaryIsCanonical :
      boundSummary ≡ diameter2BoundReading

    failClosedSummary :
      String

    failClosedSummaryIsCanonical :
      failClosedSummary ≡ diameter2FailClosedReading

    suppressionSummary :
      String

    suppressionSummaryIsCanonical :
      suppressionSummary ≡ diameter2SuppressionReading

open YMActualKPLocalSumDiameter2Receipt public

canonicalYMActualKPLocalSumDiameter2Receipt :
  YMActualKPLocalSumDiameter2Receipt
canonicalYMActualKPLocalSumDiameter2Receipt =
  record
    { status =
        actualKPLocalSumDiameter2FiniteBoundRecorded
    ; statusIsCanonical =
        refl
    ; actualActivityReceipt =
        Activity.canonicalYMActualP7WilsonPolymerActivityReceipt
    ; actualActivityDefined =
        refl
    ; sourceNowRecordsGlobalLocalSum =
        refl
    ; diameter1Receipt =
        D1.canonicalYMActualKPLocalSumDiameter1Receipt
    ; diameter1FiniteBoundClosed =
        refl
    ; diameter1GlobalKPStillOpen =
        refl
    ; boundKind =
        p7TwoStepNonBacktrackingEnvelope
    ; boundKindIsP7TwoStep =
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
        canonicalDiameter2LocalSumEnvelope
    ; envelopeIsCanonical =
        refl
    ; finiteDiameterLocalSumBelowOne =
        diameter2LocalSumBelowOne
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
    ; balabanRGTransferClosed =
        false
    ; balabanRGTransferClosedIsFalse =
        refl
    ; globalKPLocalSumClosed =
        false
    ; globalKPLocalSumClosedIsFalse =
        refl
    ; continuumYangMillsPromoted =
        false
    ; continuumYangMillsPromotedIsFalse =
        refl
    ; massGapPromoted =
        false
    ; massGapPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; openFlags =
        canonicalDiameter2OpenFlags
    ; openFlagsAreCanonical =
        refl
    ; nonClaims =
        canonicalDiameter2NonClaims
    ; nonClaimsAreCanonical =
        refl
    ; noPromotion =
        ymActualKPLocalSumDiameter2PromotionImpossibleHere
    ; boundSummary =
        diameter2BoundReading
    ; boundSummaryIsCanonical =
        refl
    ; failClosedSummary =
        diameter2FailClosedReading
    ; failClosedSummaryIsCanonical =
        refl
    ; suppressionSummary =
        diameter2SuppressionReading
    ; suppressionSummaryIsCanonical =
        refl
    }

canonicalDiameter2FiniteLocalSumClosed :
  finiteDiameterLocalSumClosed canonicalYMActualKPLocalSumDiameter2Receipt
  ≡
  true
canonicalDiameter2FiniteLocalSumClosed =
  refl

canonicalDiameter2GlobalKPStillOpen :
  globalKPLocalSumClosed canonicalYMActualKPLocalSumDiameter2Receipt
  ≡
  false
canonicalDiameter2GlobalKPStillOpen =
  refl

canonicalDiameter2NoMassGapPromotion :
  massGapPromoted canonicalYMActualKPLocalSumDiameter2Receipt
  ≡
  false
canonicalDiameter2NoMassGapPromotion =
  refl
