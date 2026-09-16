module DASHI.Wikimedia.IbrahimMonsterFiveOrbitD4N3BCharacterAcquisitionValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Wikimedia.IbrahimMonsterFiveOrbitD4N3BCharacterAcquisitionExact as A

kernelCharacterSourceRegression :
  A.fiveOrbitKernelCharacterSourceWritten A.currentFiveOrbitD4N3BCharacterAcquisition ≡ true
kernelCharacterSourceRegression = refl

n3bCharacterTableRegression :
  A.n3bCharacterTableSourceLocated A.currentFiveOrbitD4N3BCharacterAcquisition ≡ true
n3bCharacterTableRegression = refl

atlas42DPowerFamilyRegression :
  A.atlas42DPowerFamilyLocated A.currentFiveOrbitD4N3BCharacterAcquisition ≡ true
atlas42DPowerFamilyRegression = refl

atlas42DFourteenthPowerRegression :
  A.atlas42DFourteenthPowerTargets3A A.currentFiveOrbitD4N3BCharacterAcquisition ≡ true
atlas42DFourteenthPowerRegression = refl

oeisAtlasSameClassFirewallRegression :
  A.oeis42dAtlas42DSameClassPaid A.currentFiveOrbitD4N3BCharacterAcquisition ≡ false
oeisAtlasSameClassFirewallRegression = refl

n3bSignatureFirewallRegression :
  A.fiveOrbitSignatureLocatedInN3B A.currentFiveOrbitD4N3BCharacterAcquisition ≡ false
n3bSignatureFirewallRegression = refl

normalizerActionResidualRegression :
  A.selected3BNormalizerActionWeldStillRequired A.currentFiveOrbitD4N3BCharacterAcquisition ≡ true
normalizerActionResidualRegression = refl
