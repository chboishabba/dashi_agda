module DASHI.Physics.Closure.NSTriadKNR571CanonicalSecondMomentMagnitudeAdapterRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNR571CanonicalSecondMomentMagnitudeAdapterExact as A

canonicalConstructorClosed :
  A.r571CanonicalSecondMomentMagnitudeConstructorClosed ≡ true
canonicalConstructorClosed = refl

noPhysicalEnvelopePromoted :
  A.r571CanonicalAdapterIntroducesPhysicalEnvelopeEstimate ≡ false
noPhysicalEnvelopePromoted = refl

noR568Promoted :
  A.r571CanonicalAdapterClosesR568 ≡ false
noR568Promoted = refl
