module DASHI.Physics.Closure.NSTriadKNR571HermitianScalarizedOppositePairRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNR571HermitianScalarizedOppositePairExact as H

carrierClosed : H.hermitianOppositePairCarrierClosed ≡ true
carrierClosed = H.hermitianOppositePairCarrierClosedIsTrue

centeredIdentityClosed : H.hermitianOppositePairCenteredIdentityClosed ≡ true
centeredIdentityClosed = H.hermitianOppositePairCenteredIdentityClosedIsTrue

globalScalarStateNotIntroduced :
  H.hermitianOppositePairIntroducesGlobalScalarState ≡ false
globalScalarStateNotIntroduced = refl

envelopeEstimateNotIntroduced :
  H.hermitianOppositePairIntroducesEnvelopeEstimate ≡ false
envelopeEstimateNotIntroduced = refl

r568NotClaimed : H.hermitianOppositePairClosesR568 ≡ false
r568NotClaimed = refl
