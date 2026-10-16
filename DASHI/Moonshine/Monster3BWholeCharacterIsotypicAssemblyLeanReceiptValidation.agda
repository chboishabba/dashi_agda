module DASHI.Moonshine.Monster3BWholeCharacterIsotypicAssemblyLeanReceiptValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.Monster3BWholeCharacterIsotypicAssemblyLeanReceiptExact as Cut

assemblySourceWritten :
  Cut.classifierToIsotypicAssemblySourceWritten Cut.canonicalBoundary ≡ true
assemblySourceWritten = refl

finiteCopiesSourceWritten :
  Cut.finiteCopyLinearEquivalenceSourceWritten Cut.canonicalBoundary ≡ true
finiteCopiesSourceWritten = refl

kernelReceiptNotInvented :
  Cut.leanKernelReceiptObserved Cut.canonicalBoundary ≡ false
kernelReceiptNotInvented = refl

monsterClassifierStillSeparate :
  Cut.actualMonsterSimpleTypeClassifierPaid Cut.canonicalBoundary ≡ false
monsterClassifierStillSeparate = refl

copyCountNotInferred :
  Cut.actualCopyCountNinetyPaidByThisReceipt Cut.canonicalBoundary ≡ false
copyCountNotInferred = refl

fin90BasisNotChosen :
  Cut.fin90BasisChosenByThisReceipt Cut.canonicalBoundary ≡ false
fin90BasisNotChosen = refl
