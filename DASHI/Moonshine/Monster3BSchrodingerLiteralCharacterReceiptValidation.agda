module DASHI.Moonshine.Monster3BSchrodingerLiteralCharacterReceiptValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (_+_)

import DASHI.Moonshine.Monster3BSchrodingerLiteralCharacterReceiptExact as Receipt

basisDegree729 : Receipt.basisDegree ≡ 729
basisDegree729 = refl

heisenbergOrderThreePowerThirteen : Receipt.heisenbergOrder ≡ 1594323
heisenbergOrderThreePowerThirteen = refl

noncentralPartition :
  Receipt.nonzeroTranslationCount + Receipt.pureNonzeroModulationCount
  ≡ Receipt.noncentralCount
noncentralPartition = Receipt.noncentralPartitionCloses

literalCharacterAuditPaid :
  Receipt.literalCharacterMatchesCanonicalHeisenbergSignatureExecutable
    Receipt.canonicalBoundary ≡ true
literalCharacterAuditPaid = refl

commonFDRepStillOpen :
  Receipt.commonFDRepTransportPaidHere Receipt.canonicalBoundary ≡ false
commonFDRepStillOpen = refl

actualMonsterStillOpen :
  Receipt.actualMonsterConstituentAttachedHere Receipt.canonicalBoundary ≡ false
actualMonsterStillOpen = refl

end DASHI.Moonshine.Monster3BSchrodingerLiteralCharacterReceiptValidation
