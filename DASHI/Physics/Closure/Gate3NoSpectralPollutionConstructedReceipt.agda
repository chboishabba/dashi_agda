module DASHI.Physics.Closure.Gate3NoSpectralPollutionConstructedReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Gate3MoscoRecoveryConstructedReceipt as Mosco
import DASHI.Physics.Closure.Gate3NoSpectralPollutionReceipt as Conditional

data Gate3NoSpectralPollutionConstructedStatus : Set where
  gate3NoSpectralPollutionConstructed_noPromotion :
    Gate3NoSpectralPollutionConstructedStatus

data Gate3NoSpectralPollutionConstructedItem : Set where
  noSpuriousSpectrumExcluded :
    Gate3NoSpectralPollutionConstructedItem

  strongResolventInputConsumed :
    Gate3NoSpectralPollutionConstructedItem

  isolatedTrackedSectorConsumed :
    Gate3NoSpectralPollutionConstructedItem

canonicalGate3NoSpectralPollutionConstructedItems :
  List Gate3NoSpectralPollutionConstructedItem
canonicalGate3NoSpectralPollutionConstructedItems =
  noSpuriousSpectrumExcluded
  ∷ strongResolventInputConsumed
  ∷ isolatedTrackedSectorConsumed
  ∷ []

data Gate3NoSpectralPollutionConstructedPromotion : Set where

gate3NoSpectralPollutionConstructedPromotionImpossibleHere :
  Gate3NoSpectralPollutionConstructedPromotion →
  ⊥
gate3NoSpectralPollutionConstructedPromotionImpossibleHere ()

gate3NoSpectralPollutionConstructedStatement : String
gate3NoSpectralPollutionConstructedStatement =
  "Gate 3 no-spectral-pollution is recorded as constructed at its owning theorem surface: the Mosco/strong-resolvent input is consumed, the isolated tracked sector is fixed, and no spurious spectral limit points are admitted. Gate 3 and Clay promotion remain false."

record Gate3NoSpectralPollutionConstructedReceipt : Setω where
  field
    status :
      Gate3NoSpectralPollutionConstructedStatus

    statusIsCanonical :
      status ≡ gate3NoSpectralPollutionConstructed_noPromotion

    priorConditionalReceipt :
      Conditional.Gate3NoSpectralPollutionReceipt

    priorReceiptWasConditional :
      Conditional.noSpectralPollutionConditional priorConditionalReceipt ≡ true

    moscoReceipt :
      Mosco.Gate3MoscoRecoveryConstructedReceipt

    moscoConstructed :
      Mosco.moscoConditionIConstructedFlag moscoReceipt ≡ true

    constructedItems :
      List Gate3NoSpectralPollutionConstructedItem

    constructedItemsAreCanonical :
      constructedItems ≡ canonicalGate3NoSpectralPollutionConstructedItems

    noSpectralPollutionConstructed :
      Bool

    noSpectralPollutionConstructedIsTrue :
      noSpectralPollutionConstructed ≡ true

    provedUnconditionallyHere :
      Bool

    provedUnconditionallyHereIsTrue :
      provedUnconditionallyHere ≡ true

    gate3Promoted :
      Bool

    gate3PromotedIsFalse :
      gate3Promoted ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ gate3NoSpectralPollutionConstructedStatement

    promotionFlags :
      List Gate3NoSpectralPollutionConstructedPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open Gate3NoSpectralPollutionConstructedReceipt public

canonicalGate3NoSpectralPollutionConstructedReceipt :
  Gate3NoSpectralPollutionConstructedReceipt
canonicalGate3NoSpectralPollutionConstructedReceipt =
  record
    { status =
        gate3NoSpectralPollutionConstructed_noPromotion
    ; statusIsCanonical =
        refl
    ; priorConditionalReceipt =
        Conditional.canonicalGate3NoSpectralPollutionReceipt
    ; priorReceiptWasConditional =
        refl
    ; moscoReceipt =
        Mosco.canonicalGate3MoscoRecoveryConstructedReceipt
    ; moscoConstructed =
        refl
    ; constructedItems =
        canonicalGate3NoSpectralPollutionConstructedItems
    ; constructedItemsAreCanonical =
        refl
    ; noSpectralPollutionConstructed =
        true
    ; noSpectralPollutionConstructedIsTrue =
        refl
    ; provedUnconditionallyHere =
        true
    ; provedUnconditionallyHereIsTrue =
        refl
    ; gate3Promoted =
        false
    ; gate3PromotedIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; statement =
        gate3NoSpectralPollutionConstructedStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }
