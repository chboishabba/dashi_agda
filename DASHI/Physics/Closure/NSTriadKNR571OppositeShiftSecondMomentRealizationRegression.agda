module DASHI.Physics.Closure.NSTriadKNR571OppositeShiftSecondMomentRealizationRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNR571OppositeShiftSecondMomentRealizationExact as R

secondOrderIdentityClosed :
  R.r571OppositeShiftSecondOrderIdentityClosed ≡ true
secondOrderIdentityClosed = refl

absoluteMagnitudeBridgeClosed :
  R.r571OppositeShiftAbsoluteMagnitudeBridgeClosed ≡ true
absoluteMagnitudeBridgeClosed = refl

physicalEnvelopeStillOpen :
  R.r571OppositeShiftPhysicalEnvelopeBudgetClosed ≡ false
physicalEnvelopeStillOpen = refl

r568StillOpen :
  R.r571OppositeShiftSecondMomentClosesR568 ≡ false
r568StillOpen = refl
