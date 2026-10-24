module DASHI.Unified.TOEPrimitiveMaxCutValidation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Unified.TOEPrimitiveMaxCutExact as Primitive

monsterWrapperDebtRetired :
  Primitive.monsterGenericClassifierStillTerminal ≡ false
monsterWrapperDebtRetired = refl

gaugeWrapperDebtRetired :
  Primitive.round131AttachmentStillPrimitive ≡ false
gaugeWrapperDebtRetired = refl

pinnedIdentityWrapperDebtRetired :
  Primitive.r457PinnedConstructionIdentityStillPrimitive ≡ false
pinnedIdentityWrapperDebtRetired = refl

monsterActualLinearRestrictionStillOpen :
  Primitive.monsterActualLinearRestrictionPaid ≡ false
monsterActualLinearRestrictionStillOpen = refl

gaugePrimitiveSourceLeavesRemainOpen :
  Primitive.gaugePrimitiveSourceLeavesPaid ≡ false
gaugePrimitiveSourceLeavesRemainOpen = refl

attributionDoesNotPromoteSiblingSource :
  Primitive.siblingFormalSourceIsLocalAgdaTheorem ≡ false
attributionDoesNotPromoteSiblingSource = refl

monsterReceiptKeepsSiblingAuthority :
  Primitive.PrimitiveSourceReceipt.authority Primitive.monsterLinearHardeningReceipt
  ≡ Primitive.dashiSiblingFormalSource
monsterReceiptKeepsSiblingAuthority = refl

monsterReceiptIsNotLocalAgdaTheorem :
  Primitive.PrimitiveSourceReceipt.localAgdaTheorem Primitive.monsterLinearHardeningReceipt
  ≡ false
monsterReceiptIsNotLocalAgdaTheorem = refl

gaugeReceiptKeepsSiblingAuthority :
  Primitive.PrimitiveSourceReceipt.authority Primitive.sourceNativeTerminalReceipt
  ≡ Primitive.dashiSiblingFormalSource
gaugeReceiptKeepsSiblingAuthority = refl

gaugeReceiptIsNotLocalAgdaTheorem :
  Primitive.PrimitiveSourceReceipt.localAgdaTheorem Primitive.sourceNativeTerminalReceipt
  ≡ false
gaugeReceiptIsNotLocalAgdaTheorem = refl
