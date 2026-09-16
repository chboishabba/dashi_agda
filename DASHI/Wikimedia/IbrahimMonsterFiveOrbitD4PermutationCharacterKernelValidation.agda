module DASHI.Wikimedia.IbrahimMonsterFiveOrbitD4PermutationCharacterKernelValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Wikimedia.IbrahimMonsterFiveOrbitD4PermutationCharacterKernelExact as K

identityCharacterRegression : K.identityFixedOrbitCount ≡ 5
identityCharacterRegression = refl

halfTurnCharacterRegression : K.halfTurnFixedOrbitCount ≡ 5
halfTurnCharacterRegression = refl

quarterTurnCharacterRegression : K.quarterTurnFixedOrbitCount ≡ 1
quarterTurnCharacterRegression = refl

axisReflectionCharacterRegression : K.axisReflectionFixedOrbitCount ≡ 3
axisReflectionCharacterRegression = refl

diagonalReflectionCharacterRegression : K.diagonalReflectionFixedOrbitCount ≡ 3
diagonalReflectionCharacterRegression = refl

kernelPermutationCharacterSourceRegression :
  K.agdaKernelPermutationCharacterSourceWritten K.currentFiveOrbitD4PermutationKernelBoundary ≡ true
kernelPermutationCharacterSourceRegression = refl

kernelPermutationCharacterReceiptStillUnpaidRegression :
  K.agdaKernelPermutationCharacterObserved K.currentFiveOrbitD4PermutationKernelBoundary ≡ false
kernelPermutationCharacterReceiptStillUnpaidRegression = refl

kernelDecompositionStillUnpaidRegression :
  K.agdaKernelIrrepDecompositionObserved K.currentFiveOrbitD4PermutationKernelBoundary ≡ false
kernelDecompositionStillUnpaidRegression = refl

monsterActionFirewallRegression :
  K.characterBridgeCreatesMonster42dAction K.currentFiveOrbitD4PermutationKernelBoundary ≡ false
monsterActionFirewallRegression = refl
