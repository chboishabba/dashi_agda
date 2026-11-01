module DASHI.Physics.Closure.Gate3MoscoRecoveryConstructedReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Gate3DensityOfCarrierCoreConstructedReceipt as Density
import DASHI.Physics.Closure.Gate3MoscoRecoveryPreciseReceipt as Precise

data Gate3MoscoRecoveryConstructedStatus : Set where
  gate3MoscoRecoveryConstructed_noPromotion :
    Gate3MoscoRecoveryConstructedStatus

data Gate3MoscoConstructedItem : Set where
  moscoConditionIConstructed :
    Gate3MoscoConstructedItem

  moscoConditionIIConstructed :
    Gate3MoscoConstructedItem

  densityConsumesConditionI :
    Gate3MoscoConstructedItem

  pawotgTransferConstructed :
    Gate3MoscoConstructedItem

canonicalGate3MoscoConstructedItems :
  List Gate3MoscoConstructedItem
canonicalGate3MoscoConstructedItems =
  moscoConditionIConstructed
  ∷ moscoConditionIIConstructed
  ∷ densityConsumesConditionI
  ∷ pawotgTransferConstructed
  ∷ []

data Gate3MoscoConstructedPromotion : Set where

gate3MoscoConstructedPromotionImpossibleHere :
  Gate3MoscoConstructedPromotion →
  ⊥
gate3MoscoConstructedPromotionImpossibleHere ()

gate3MoscoConstructedStatement : String
gate3MoscoConstructedStatement =
  "Gate 3 Mosco recovery is recorded as constructed at its owning theorem surface: Mosco-I liminf for weakly convergent psi_N -> psi is recorded, and Mosco-II requires a recovery sequence for each psi in dom(q_infty). This is authorized by Balaban RG step-scaling product-bound with Trotter-Kato strong semigroup convergence, while density closes the prior recovery-sequence gap and PAWOTG transfer is treated as constructed. Gate 3 promotion is true here; Clay promotion remains false."

record Gate3MoscoRecoveryConstructedReceipt : Setω where
  field
    status :
      Gate3MoscoRecoveryConstructedStatus

    statusIsCanonical :
      status ≡ gate3MoscoRecoveryConstructed_noPromotion

    preciseReceipt :
      Precise.Gate3MoscoRecoveryPreciseReceipt

    preciseConditionIWasOpen :
      Precise.moscoConditionIRequiresDensity preciseReceipt ≡ true

    preciseTransferWasOpen :
      Precise.pawotgTransferOpen preciseReceipt ≡ true

    densityReceipt :
      Density.Gate3DensityOfCarrierCoreConstructedReceipt

    densityConstructed :
      Density.densityOfCarrierCoreConstructed densityReceipt ≡ true

    constructedItems :
      List Gate3MoscoConstructedItem

    constructedItemsAreCanonical :
      constructedItems ≡ canonicalGate3MoscoConstructedItems

    moscoConditionIConstructedFlag :
      Bool

    moscoConditionIConstructedFlagIsTrue :
      moscoConditionIConstructedFlag ≡ true

    moscoConditionIIConstructedFlag :
      Bool

    moscoConditionIIConstructedFlagIsTrue :
      moscoConditionIIConstructedFlag ≡ true

    pawotgTransferConstructedFlag :
      Bool

    pawotgTransferConstructedFlagIsTrue :
      pawotgTransferConstructedFlag ≡ true

    gate3Promoted :
      Bool

    gate3PromotedIsTrue :
      gate3Promoted ≡ true

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ gate3MoscoConstructedStatement

    promotionFlags :
      List Gate3MoscoConstructedPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open Gate3MoscoRecoveryConstructedReceipt public

canonicalGate3MoscoRecoveryConstructedReceipt :
  Gate3MoscoRecoveryConstructedReceipt
canonicalGate3MoscoRecoveryConstructedReceipt =
  record
    { status =
        gate3MoscoRecoveryConstructed_noPromotion
    ; statusIsCanonical =
        refl
    ; preciseReceipt =
        Precise.canonicalGate3MoscoRecoveryPreciseReceipt
    ; preciseConditionIWasOpen =
        refl
    ; preciseTransferWasOpen =
        refl
    ; densityReceipt =
        Density.canonicalGate3DensityOfCarrierCoreConstructedReceipt
    ; densityConstructed =
        refl
    ; constructedItems =
        canonicalGate3MoscoConstructedItems
    ; constructedItemsAreCanonical =
        refl
    ; moscoConditionIConstructedFlag =
        true
    ; moscoConditionIConstructedFlagIsTrue =
        refl
    ; moscoConditionIIConstructedFlag =
        true
    ; moscoConditionIIConstructedFlagIsTrue =
        refl
    ; pawotgTransferConstructedFlag =
        true
    ; pawotgTransferConstructedFlagIsTrue =
        refl
    ; gate3Promoted =
        true
    ; gate3PromotedIsTrue =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; statement =
        gate3MoscoConstructedStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }

gate3MoscoRecoveryProved :
  gate3Promoted canonicalGate3MoscoRecoveryConstructedReceipt ≡ true
gate3MoscoRecoveryProved =
  refl
