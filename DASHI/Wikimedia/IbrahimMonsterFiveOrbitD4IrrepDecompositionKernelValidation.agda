module DASHI.Wikimedia.IbrahimMonsterFiveOrbitD4IrrepDecompositionKernelValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Wikimedia.IbrahimMonsterFiveOrbitD4IrrepDecompositionKernelExact as K

a1MultiplicityRegression : K.a1Multiplicity ≡ 3
a1MultiplicityRegression = refl

a2MultiplicityRegression : K.a2Multiplicity ≡ 0
a2MultiplicityRegression = refl

b1MultiplicityRegression : K.b1Multiplicity ≡ 1
b1MultiplicityRegression = refl

b2MultiplicityRegression : K.b2Multiplicity ≡ 1
b2MultiplicityRegression = refl

eMultiplicityRegression : K.eMultiplicity ≡ 0
eMultiplicityRegression = refl

characterDecompositionSourceRegression :
  K.agdaKernelIrrepDecompositionSourceWritten K.currentFiveOrbitD4IrrepKernelBoundary ≡ true
characterDecompositionSourceRegression = refl

kernelReceiptStillUnpaidRegression :
  K.agdaKernelIrrepDecompositionObserved K.currentFiveOrbitD4IrrepKernelBoundary ≡ false
kernelReceiptStillUnpaidRegression = refl

monster42dFirewallRegression :
  K.irrepDecompositionCreatesMonster42dAction K.currentFiveOrbitD4IrrepKernelBoundary ≡ false
monster42dFirewallRegression = refl
