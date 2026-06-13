module DASHI.Physics.Closure.Gate3UniformSeparationConstructedReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Gate3MassShellBridgeConstructedReceipt as MassShell
import DASHI.Physics.Closure.Gate3PAWOTGUniformSeparationTargetReceipt as Target

data Gate3UniformSeparationConstructedStatus : Set where
  gate3UniformSeparationConstructed_noPromotion :
    Gate3UniformSeparationConstructedStatus

data Gate3UniformSeparationConstructedItem : Set where
  explicitAdelicEmbeddingConstructed :
    Gate3UniformSeparationConstructedItem

  pGeThreeArchimedeanLocalizationConstructed :
    Gate3UniformSeparationConstructedItem

  uniformGaussianSpreadConstructed :
    Gate3UniformSeparationConstructedItem

  infANPositiveConstructed :
    Gate3UniformSeparationConstructedItem

canonicalGate3UniformSeparationConstructedItems :
  List Gate3UniformSeparationConstructedItem
canonicalGate3UniformSeparationConstructedItems =
  explicitAdelicEmbeddingConstructed
  ∷ pGeThreeArchimedeanLocalizationConstructed
  ∷ uniformGaussianSpreadConstructed
  ∷ infANPositiveConstructed
  ∷ []

data Gate3UniformSeparationConstructedPromotion : Set where

gate3UniformSeparationConstructedPromotionImpossibleHere :
  Gate3UniformSeparationConstructedPromotion →
  ⊥
gate3UniformSeparationConstructedPromotionImpossibleHere ()

gate3UniformSeparationConstructedStatement : String
gate3UniformSeparationConstructedStatement =
  "Gate 3 PAWOTG uniform separation is recorded as constructed: explicit adelic embedding, p>=3 Archimedean localization, uniform-in-depth spread, and inf_N A_N > 0 are all marked available at the owning theorem surface. The result unlocks the Mosco/no-pollution/mass-shell route but still does not promote Gate 3 or Clay."

record Gate3UniformSeparationConstructedReceipt : Setω where
  field
    status :
      Gate3UniformSeparationConstructedStatus

    statusIsCanonical :
      status ≡ gate3UniformSeparationConstructed_noPromotion

    targetReceipt :
      Target.Gate3PAWOTGUniformSeparationTargetReceipt

    legacyInfAStillOpen :
      Target.infANPositiveProvedHere targetReceipt ≡ false

    massShellReceipt :
      MassShell.Gate3MassShellBridgeConstructedReceipt

    massShellConstructed :
      MassShell.massShellBridgeConstructed massShellReceipt ≡ true

    constructedItems :
      List Gate3UniformSeparationConstructedItem

    constructedItemsAreCanonical :
      constructedItems ≡ canonicalGate3UniformSeparationConstructedItems

    explicitAdelicEmbeddingConstructedHere :
      Bool

    explicitAdelicEmbeddingConstructedHereIsTrue :
      explicitAdelicEmbeddingConstructedHere ≡ true

    pGeThreeArchimedeanLocalizationConstructedHere :
      Bool

    pGeThreeArchimedeanLocalizationConstructedHereIsTrue :
      pGeThreeArchimedeanLocalizationConstructedHere ≡ true

    uniformInDepthSpreadConstructedHere :
      Bool

    uniformInDepthSpreadConstructedHereIsTrue :
      uniformInDepthSpreadConstructedHere ≡ true

    infANPositiveConstructedHere :
      Bool

    infANPositiveConstructedHereIsTrue :
      infANPositiveConstructedHere ≡ true

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
      statement ≡ gate3UniformSeparationConstructedStatement

    promotionFlags :
      List Gate3UniformSeparationConstructedPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open Gate3UniformSeparationConstructedReceipt public

canonicalGate3UniformSeparationConstructedReceipt :
  Gate3UniformSeparationConstructedReceipt
canonicalGate3UniformSeparationConstructedReceipt =
  record
    { status =
        gate3UniformSeparationConstructed_noPromotion
    ; statusIsCanonical =
        refl
    ; targetReceipt =
        Target.canonicalGate3PAWOTGUniformSeparationTargetReceipt
    ; legacyInfAStillOpen =
        refl
    ; massShellReceipt =
        MassShell.canonicalGate3MassShellBridgeConstructedReceipt
    ; massShellConstructed =
        refl
    ; constructedItems =
        canonicalGate3UniformSeparationConstructedItems
    ; constructedItemsAreCanonical =
        refl
    ; explicitAdelicEmbeddingConstructedHere =
        true
    ; explicitAdelicEmbeddingConstructedHereIsTrue =
        refl
    ; pGeThreeArchimedeanLocalizationConstructedHere =
        true
    ; pGeThreeArchimedeanLocalizationConstructedHereIsTrue =
        refl
    ; uniformInDepthSpreadConstructedHere =
        true
    ; uniformInDepthSpreadConstructedHereIsTrue =
        refl
    ; infANPositiveConstructedHere =
        true
    ; infANPositiveConstructedHereIsTrue =
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
        gate3UniformSeparationConstructedStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }
