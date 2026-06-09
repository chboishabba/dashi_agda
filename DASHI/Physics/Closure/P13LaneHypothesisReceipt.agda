module DASHI.Physics.Closure.P13LaneHypothesisReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- p13 lane-hypothesis diagnostic receipt.
--
-- Prime 13 is recorded as the T13 source seen in the deg23 discussion, but
-- this receipt does not promote it to a carrier prime lane.  The finite
-- point-count check for E_{j=0}: y^2 = x^3 + 1 over F13 gives 11 affine
-- points plus the point at infinity, hence #E(F13)=12.  Equivalently
-- a_13 = 13 + 1 - 12 = 2 for this model.  Therefore the point count is not
-- 14 and does not itself explain deg23.

data P13LaneHypothesisStatus : Set where
  p13LaneHypothesisDiagnosticFalseOpen :
    P13LaneHypothesisStatus

data P13LaneHypothesisBlocker : Set where
  t13SourceDoesNotMakeCarrierPrimeLane :
    P13LaneHypothesisBlocker

  eJ0F13PointCountIsTwelveNotFourteen :
    P13LaneHypothesisBlocker

  pointCountDoesNotExplainDeg23 :
    P13LaneHypothesisBlocker

  missingCKMPromotion :
    P13LaneHypothesisBlocker

  missingSMPromotion :
    P13LaneHypothesisBlocker

  missingTerminalClosure :
    P13LaneHypothesisBlocker

canonicalP13LaneHypothesisBlockers :
  List P13LaneHypothesisBlocker
canonicalP13LaneHypothesisBlockers =
  t13SourceDoesNotMakeCarrierPrimeLane
  ∷ eJ0F13PointCountIsTwelveNotFourteen
  ∷ pointCountDoesNotExplainDeg23
  ∷ missingCKMPromotion
  ∷ missingSMPromotion
  ∷ missingTerminalClosure
  ∷ []

data P13LaneHypothesisPromotion : Set where

p13LaneHypothesisPromotionImpossibleHere :
  P13LaneHypothesisPromotion →
  ⊥
p13LaneHypothesisPromotionImpossibleHere ()

p13T13SourceLabel : String
p13T13SourceLabel =
  "prime 13 appears as T13 source of deg23, but not as a carrier prime lane"

eJ0F13EquationLabel : String
eJ0F13EquationLabel =
  "E_{j=0}/F13: y^2 = x^3 + 1"

eJ0F13PerXAffineCountsLabel : String
eJ0F13PerXAffineCountsLabel =
  "x=0..12 solution counts: 2,0,2,0,1,2,2,0,0,0,1,0,1"

record P13LaneHypothesisReceipt : Set where
  field
    status :
      P13LaneHypothesisStatus

    p13Prime :
      Nat

    p13PrimeIsThirteen :
      p13Prime ≡ 13

    t13SourceRecorded :
      Bool

    t13SourceRecordedIsTrue :
      t13SourceRecorded ≡ true

    t13SourceStatement :
      String

    t13SourceStatementIsCanonical :
      t13SourceStatement ≡ p13T13SourceLabel

    carrierPrimeLane :
      Bool

    carrierPrimeLaneIsFalse :
      carrierPrimeLane ≡ false

    ellipticCurveLabel :
      String

    ellipticCurveLabelIsCanonical :
      ellipticCurveLabel ≡ eJ0F13EquationLabel

    perXAffineCounts :
      String

    perXAffineCountsIsCanonical :
      perXAffineCounts ≡ eJ0F13PerXAffineCountsLabel

    affineSolutionsOverF13 :
      Nat

    affineSolutionsOverF13IsEleven :
      affineSolutionsOverF13 ≡ 11

    pointAtInfinity :
      Nat

    pointAtInfinityIsOne :
      pointAtInfinity ≡ 1

    totalPointsOverF13 :
      Nat

    totalPointsOverF13IsAffinePlusInfinity :
      totalPointsOverF13 ≡ affineSolutionsOverF13 + pointAtInfinity

    totalPointsOverF13IsTwelve :
      totalPointsOverF13 ≡ 12

    f13BasePlusOne :
      Nat

    f13BasePlusOneIsFourteen :
      f13BasePlusOne ≡ 14

    a13Trace :
      Nat

    a13TraceIsTwo :
      a13Trace ≡ 2

    pointCountIsFourteen :
      Bool

    pointCountIsFourteenIsFalse :
      pointCountIsFourteen ≡ false

    pointCountExplainsDeg23 :
      Bool

    pointCountExplainsDeg23IsFalse :
      pointCountExplainsDeg23 ≡ false

    laneHypothesisDiagnostic :
      Bool

    laneHypothesisDiagnosticIsFalse :
      laneHypothesisDiagnostic ≡ false

    laneHypothesisOpen :
      Bool

    laneHypothesisOpenIsTrue :
      laneHypothesisOpen ≡ true

    ckmPromotion :
      Bool

    ckmPromotionIsFalse :
      ckmPromotion ≡ false

    smPromotion :
      Bool

    smPromotionIsFalse :
      smPromotion ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    blockers :
      List P13LaneHypothesisBlocker

    blockersAreCanonical :
      blockers ≡ canonicalP13LaneHypothesisBlockers

    promotionFlags :
      List P13LaneHypothesisPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open P13LaneHypothesisReceipt public

canonicalP13LaneHypothesisReceipt :
  P13LaneHypothesisReceipt
canonicalP13LaneHypothesisReceipt =
  record
    { status =
        p13LaneHypothesisDiagnosticFalseOpen
    ; p13Prime =
        13
    ; p13PrimeIsThirteen =
        refl
    ; t13SourceRecorded =
        true
    ; t13SourceRecordedIsTrue =
        refl
    ; t13SourceStatement =
        p13T13SourceLabel
    ; t13SourceStatementIsCanonical =
        refl
    ; carrierPrimeLane =
        false
    ; carrierPrimeLaneIsFalse =
        refl
    ; ellipticCurveLabel =
        eJ0F13EquationLabel
    ; ellipticCurveLabelIsCanonical =
        refl
    ; perXAffineCounts =
        eJ0F13PerXAffineCountsLabel
    ; perXAffineCountsIsCanonical =
        refl
    ; affineSolutionsOverF13 =
        11
    ; affineSolutionsOverF13IsEleven =
        refl
    ; pointAtInfinity =
        1
    ; pointAtInfinityIsOne =
        refl
    ; totalPointsOverF13 =
        12
    ; totalPointsOverF13IsAffinePlusInfinity =
        refl
    ; totalPointsOverF13IsTwelve =
        refl
    ; f13BasePlusOne =
        14
    ; f13BasePlusOneIsFourteen =
        refl
    ; a13Trace =
        2
    ; a13TraceIsTwo =
        refl
    ; pointCountIsFourteen =
        false
    ; pointCountIsFourteenIsFalse =
        refl
    ; pointCountExplainsDeg23 =
        false
    ; pointCountExplainsDeg23IsFalse =
        refl
    ; laneHypothesisDiagnostic =
        false
    ; laneHypothesisDiagnosticIsFalse =
        refl
    ; laneHypothesisOpen =
        true
    ; laneHypothesisOpenIsTrue =
        refl
    ; ckmPromotion =
        false
    ; ckmPromotionIsFalse =
        refl
    ; smPromotion =
        false
    ; smPromotionIsFalse =
        refl
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    ; blockers =
        canonicalP13LaneHypothesisBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Prime 13 is recorded only as the T13 source of deg23"
        ∷ "Prime 13 is not promoted to a carrier prime lane"
        ∷ "For E_{j=0}: y^2=x^3+1 over F13, the affine solution count is 11"
        ∷ "Adding the point at infinity gives #E(F13)=12, so a_13=13+1-12=2"
        ∷ "The point count is not 14 and does not itself explain deg23"
        ∷ "p13 lane hypothesis diagnostic is false/open; CKM, SM, and terminal flags are false"
        ∷ []
    }

p13IsT13SourceButNotCarrierLane :
  carrierPrimeLane canonicalP13LaneHypothesisReceipt ≡ false
p13IsT13SourceButNotCarrierLane =
  refl

p13EJ0F13PointCountIsTwelve :
  totalPointsOverF13 canonicalP13LaneHypothesisReceipt ≡ 12
p13EJ0F13PointCountIsTwelve =
  refl

p13EJ0F13PointCountIsNotFourteen :
  pointCountIsFourteen canonicalP13LaneHypothesisReceipt ≡ false
p13EJ0F13PointCountIsNotFourteen =
  refl

p13LaneHypothesisDiagnosticRemainsFalse :
  laneHypothesisDiagnostic canonicalP13LaneHypothesisReceipt ≡ false
p13LaneHypothesisDiagnosticRemainsFalse =
  refl

p13LaneHypothesisNoTerminalPromotion :
  terminalPromotion canonicalP13LaneHypothesisReceipt ≡ false
p13LaneHypothesisNoTerminalPromotion =
  refl
