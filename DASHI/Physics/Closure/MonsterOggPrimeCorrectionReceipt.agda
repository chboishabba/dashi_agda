module DASHI.Physics.Closure.MonsterOggPrimeCorrectionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.MonsterIrrepCarrierDecompositionReceipt
  as Monster

------------------------------------------------------------------------
-- Monster / Ogg prime correction receipt.
--
-- This receipt is intentionally narrow.  It records that the Monster's 194
-- conjugacy-class / irrep lanes and the 15 Ogg/supersingular prime lanes are
-- different indexing sets.  Therefore "15 + 179" is carrier quotient
-- bookkeeping, not a genus-zero/genus-positive partition.

data MonsterOggPrimeCorrectionStatus : Set where
  monsterOggPrimeCorrectionRecorded_noPromotion :
    MonsterOggPrimeCorrectionStatus

data MonsterOggIndexingDatum : Set where
  monsterConjugacyClassLanes194 :
    MonsterOggIndexingDatum

  mckayThompsonHauptmodulLanesRecordedForMonsterClasses :
    MonsterOggIndexingDatum

  oggSupersingularPrimeCarrierLanes15 :
    MonsterOggIndexingDatum

  nonCarrierBookkeepingRemainder179 :
    MonsterOggIndexingDatum

  indexingSetsAreDistinct :
    MonsterOggIndexingDatum

canonicalMonsterOggIndexingData : List MonsterOggIndexingDatum
canonicalMonsterOggIndexingData =
  monsterConjugacyClassLanes194
  ∷ mckayThompsonHauptmodulLanesRecordedForMonsterClasses
  ∷ oggSupersingularPrimeCarrierLanes15
  ∷ nonCarrierBookkeepingRemainder179
  ∷ indexingSetsAreDistinct
  ∷ []

data MonsterOggRejectedPromotion : Set where

monsterOggRejectedPromotionImpossibleHere :
  MonsterOggRejectedPromotion →
  ⊥
monsterOggRejectedPromotionImpossibleHere ()

monsterClassLaneCount :
  Nat
monsterClassLaneCount =
  194

oggPrimeCarrierLaneCount :
  Nat
oggPrimeCarrierLaneCount =
  15

nonCarrierBookkeepingCount :
  Nat
nonCarrierBookkeepingCount =
  179

monsterOggCorrectionStatement :
  String
monsterOggCorrectionStatement =
  "The Monster 194 conjugacy lanes and the 15 Ogg/supersingular prime carrier lanes are distinct indexing sets; 179 is quotient bookkeeping, not a genus-positive McKay-Thompson partition."

record MonsterOggPrimeCorrectionReceipt : Setω where
  field
    status :
      MonsterOggPrimeCorrectionStatus

    statusIsCanonical :
      status ≡ monsterOggPrimeCorrectionRecorded_noPromotion

    monsterIrrepReceipt :
      Monster.MonsterIrrepCarrierDecompositionReceipt

    monsterReceiptRecordsAll194HauptmodulLanes :
      Monster.all194McKayThompsonHauptmodulLanesRecorded
        monsterIrrepReceipt
      ≡
      true

    monsterReceiptRejectsGenusPositive179 :
      Monster.claim179HaveGenusPositiveMcKayThompsonSeries
        monsterIrrepReceipt
      ≡
      false

    monsterReceiptKeepsYMClayFalse :
      Monster.clayYangMillsPromoted monsterIrrepReceipt ≡ false

    indexingData :
      List MonsterOggIndexingDatum

    indexingDataAreCanonical :
      indexingData ≡ canonicalMonsterOggIndexingData

    monsterClasses :
      Nat

    monsterClassesIs194 :
      monsterClasses ≡ monsterClassLaneCount

    oggPrimeCarriers :
      Nat

    oggPrimeCarriersIs15 :
      oggPrimeCarriers ≡ oggPrimeCarrierLaneCount

    nonCarrierRemainder :
      Nat

    nonCarrierRemainderIs179 :
      nonCarrierRemainder ≡ nonCarrierBookkeepingCount

    all194HauptmodulLaneCorrectionRecorded :
      Bool

    all194HauptmodulLaneCorrectionRecordedIsTrue :
      all194HauptmodulLaneCorrectionRecorded ≡ true

    fifteenPlus179GenusPartitionClaim :
      Bool

    fifteenPlus179GenusPartitionClaimIsFalse :
      fifteenPlus179GenusPartitionClaim ≡ false

    gate3Promoted :
      Bool

    gate3PromotedIsFalse :
      gate3Promoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalPromoted :
      Bool

    terminalPromotedIsFalse :
      terminalPromoted ≡ false

    promotions :
      List MonsterOggRejectedPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      MonsterOggRejectedPromotion →
      ⊥

    correctionText :
      String

    correctionTextIsCanonical :
      correctionText ≡ monsterOggCorrectionStatement

open MonsterOggPrimeCorrectionReceipt public

canonicalMonsterOggPrimeCorrectionReceipt :
  MonsterOggPrimeCorrectionReceipt
canonicalMonsterOggPrimeCorrectionReceipt =
  record
    { status =
        monsterOggPrimeCorrectionRecorded_noPromotion
    ; statusIsCanonical =
        refl
    ; monsterIrrepReceipt =
        Monster.canonicalMonsterIrrepCarrierDecompositionReceipt
    ; monsterReceiptRecordsAll194HauptmodulLanes =
        refl
    ; monsterReceiptRejectsGenusPositive179 =
        refl
    ; monsterReceiptKeepsYMClayFalse =
        refl
    ; indexingData =
        canonicalMonsterOggIndexingData
    ; indexingDataAreCanonical =
        refl
    ; monsterClasses =
        monsterClassLaneCount
    ; monsterClassesIs194 =
        refl
    ; oggPrimeCarriers =
        oggPrimeCarrierLaneCount
    ; oggPrimeCarriersIs15 =
        refl
    ; nonCarrierRemainder =
        nonCarrierBookkeepingCount
    ; nonCarrierRemainderIs179 =
        refl
    ; all194HauptmodulLaneCorrectionRecorded =
        true
    ; all194HauptmodulLaneCorrectionRecordedIsTrue =
        refl
    ; fifteenPlus179GenusPartitionClaim =
        false
    ; fifteenPlus179GenusPartitionClaimIsFalse =
        refl
    ; gate3Promoted =
        false
    ; gate3PromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalPromoted =
        false
    ; terminalPromotedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        monsterOggRejectedPromotionImpossibleHere
    ; correctionText =
        monsterOggCorrectionStatement
    ; correctionTextIsCanonical =
        refl
    }

monsterOggCorrectionRejectsGenusPartition :
  fifteenPlus179GenusPartitionClaim
    canonicalMonsterOggPrimeCorrectionReceipt
  ≡
  false
monsterOggCorrectionRejectsGenusPartition =
  refl

monsterOggCorrectionKeepsYMFalse :
  clayYangMillsPromoted canonicalMonsterOggPrimeCorrectionReceipt
  ≡
  false
monsterOggCorrectionKeepsYMFalse =
  refl
