module DASHI.Physics.Closure.NSTriadKNR571SecondOrderAbsoluteMagnitudeRegression where

-- RED/GREEN regression for the purely algebraic bridge from the existing
-- signed paired second-order defect to the existing nonnegative second-moment
-- magnitude carrier.  This must not pay any physical Taylor-envelope or R568
-- estimate.

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNLuoPairedSecondOrderAbsoluteMagnitudeBridgeExact as Abs
import DASHI.Physics.Closure.NSTriadKNR571HomochiralPairedSecondMomentRealizationExact as R

absoluteMagnitudeCarrierClosed :
  Abs.roundAbsoluteMagnitudeCarrierClosed ≡ true
absoluteMagnitudeCarrierClosed = refl

signedDefectToMagnitudeClosed :
  Abs.roundSignedDefectToMagnitudeClosed ≡ true
signedDefectToMagnitudeClosed = refl

physicalEnvelopeStillOpen :
  R.r571PhysicalSecondMomentEnvelopeBudgetClosed ≡ false
physicalEnvelopeStillOpen = refl

r568StillOpen :
  R.r571R568SpacetimeBudgetClosedHere ≡ false
r568StillOpen = refl
