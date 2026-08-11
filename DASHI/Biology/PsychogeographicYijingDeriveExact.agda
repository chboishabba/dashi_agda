module DASHI.Biology.PsychogeographicYijingDeriveExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Vec using (Vec) renaming ([] to vnil; _∷_ to _vcons_)

import DASHI.Biology.DASHIYijingTernaryDivinationExact as Yijing
import DASHI.Biology.DASHIYijingRelationalOperatorsExact as Relational
import DASHI.Biology.PsychogeographicFieldExact as Field
import DASHI.Biology.PsychogeographicHexagramObservationExact as Observation

------------------------------------------------------------------------
-- A cast configures an attention/route policy.  The encountered landscape may
-- preserve, reject or transform that initial reading.  No external prediction
-- constructor is required by the derive.
------------------------------------------------------------------------

data StructuredChanceSource : Set where
  coinCast : StructuredChanceSource
  yarrowCast : StructuredChanceSource
  intersectionChoice : StructuredChanceSource
  blockedRoadChoice : StructuredChanceSource
  overheardPhraseChoice : StructuredChanceSource
  weatherShiftChoice : StructuredChanceSource

record PsychogeographicDerivePlan : Set where
  constructor psychogeographicDerivePlan
  field
    chanceSource : StructuredChanceSource
    initialHexagram : Yijing.TernaryHexagram
    lowerAttention : Observation.EnvironmentalPrompt
    upperAttention : Observation.EnvironmentalPrompt
    movingMask : Vec Bool 6
    plannedSteps : List Field.RouteStep
    encounteredHexagram : Yijing.TernaryHexagram
    readingAuthority : Yijing.ReadingAuthority
    planReceipt : String

open PsychogeographicDerivePlan public

canonicalPsychogeographicDerive : PsychogeographicDerivePlan
canonicalPsychogeographicDerive =
  psychogeographicDerivePlan
    coinCast
    Relational.canonicalCastInitial
    Observation.channelDangerPrompt
    Observation.gatheringExchangePrompt
    Relational.canonicalCastMask
    (Field.leaveHabitualRoute
      ∷ Field.followWaterChannel
      ∷ Field.circleChurchThreshold
      ∷ Field.enterRuin
      ∷ [])
    Relational.canonicalCastResulting
    Yijing.associativeAuthority
    "cast -> attention policy -> walk -> encountered reading"

canonicalLowerTrigramIsWater :
  Relational.observeTrigramImage
    (Relational.lowerTrigram (initialHexagram canonicalPsychogeographicDerive))
  ≡ Relational.receivedImage Relational.waterImage
canonicalLowerTrigramIsWater = refl

canonicalUpperTrigramIsLake :
  Relational.observeTrigramImage
    (Relational.upperTrigram (initialHexagram canonicalPsychogeographicDerive))
  ≡ Relational.receivedImage Relational.lakeMarshImage
canonicalUpperTrigramIsLake = refl

canonicalDeriveDifferenceIsTwo :
  Observation.hexagramDifference
    (initialHexagram canonicalPsychogeographicDerive)
    (encounteredHexagram canonicalPsychogeographicDerive)
  ≡ 2
canonicalDeriveDifferenceIsTwo = refl

canonicalDeriveUsesAssociativeNotPredictiveAuthority :
  readingAuthority canonicalPsychogeographicDerive
  ≡ Yijing.associativeAuthority
canonicalDeriveUsesAssociativeNotPredictiveAuthority = refl

record PsychogeographicYijingDeriveBoundary : Set where
  constructor psychogeographicYijingDeriveBoundary
  field
    structuredChancePredictsExternalFuture : Bool
    structuredChancePredictsExternalFutureIsFalse :
      structuredChancePredictsExternalFuture ≡ false
    castMayInterruptHabitualRouteSelection : Bool
    castMayInterruptHabitualRouteSelectionIsTrue :
      castMayInterruptHabitualRouteSelection ≡ true
    encounteredDifferenceIsFailureOfPractice : Bool
    encounteredDifferenceIsFailureOfPracticeIsFalse :
      encounteredDifferenceIsFailureOfPractice ≡ false
    environmentalPromptIsFixedTrigramTranslation : Bool
    environmentalPromptIsFixedTrigramTranslationIsFalse :
      environmentalPromptIsFixedTrigramTranslation ≡ false

canonicalPsychogeographicYijingDeriveBoundary :
  PsychogeographicYijingDeriveBoundary
canonicalPsychogeographicYijingDeriveBoundary =
  psychogeographicYijingDeriveBoundary false refl true refl false refl false refl
