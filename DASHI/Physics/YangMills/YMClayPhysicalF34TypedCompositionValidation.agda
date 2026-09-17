module DASHI.Physics.YangMills.YMClayPhysicalF34TypedCompositionValidation where

open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.YangMills.YMClayPhysicalF34TypedCompositionExact as Typed

f3RecoveryGapIsCompilerOutput :
  Typed.f3RecoveryGapRequiresIndependentPayment ≡ false
f3RecoveryGapIsCompilerOutput =
  Typed.f3RecoveryGapRequiresIndependentPaymentIsFalse

f4EvolutionEqualityIsStoredPhysicalPayment :
  Typed.f4EvolutionEqualityRequiresAnotherSameObjectAxiom ≡ false
f4EvolutionEqualityIsStoredPhysicalPayment =
  Typed.f4EvolutionEqualityRequiresAnotherSameObjectAxiomIsFalse

legacyReceiptBitsDoNotPayTypedF34 :
  Typed.legacyBooleanReceiptsPayTypedPhysicalF34 ≡ false
legacyReceiptBitsDoNotPayTypedF34 =
  Typed.legacyBooleanReceiptsPayTypedPhysicalF34IsFalse

typedF34CompositionIsAvailable :
  Typed.typedF34CompositionCompilerOwned ≡ true
typedF34CompositionIsAvailable =
  Typed.typedF34CompositionCompilerOwnedIsTrue
